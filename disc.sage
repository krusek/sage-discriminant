from sage.ext.fast_eval import fast_float_constant
from sage.plot.plot3d.list_plot3d import list_plot3d_tuples
from sage.plot.plot3d.shapes2 import Line as Line3d

### constants

TOLERANCE = 1e-6

def equals(a, b):
  return abs(a-b) <= TOLERANCE

def is_zero(a):
  return equals(a, 0)

def distance_squared(p1, p2):
  assert(len(p1) == len(p2))
  return sum(map(lambda x: x*x, map(lambda x: x[0] - x[1], zip(p1, p2))))

def evalf(v):
  if type(v) == list:
    return list(map(lambda x: evalf(x), v))
  if type(v) == tuple:
    return tuple(map(lambda x: evalf(x), v))
  return fast_float_constant(v)()

### shapes.sage

class Line:
  """
  A line given as a [point] and a [vector]. Currently only two dimensions are supported.
  [point] and [vector] are expected to be the same length (assertions fail other wise).

  If [point] = (px,py) and [vector] = (vx, vy) then the line can also be represented as
  vy*x - vx*y + (vx*py - vy*px) = 0
  """
  def __init__(self, point, vector):
    self.point = point
    self.vector = vector
    assert(len(point) == len(vector))
    assert(len(point) == 2)
  
  def intersect(self, line):
    """Find the intersection of this line with [line]. If these lines do not intersect
    then None is returned.

    Args:
        line (Line): The other line to intersect with.
    """
    a1 = self.vector[1]
    b1 = -self.vector[0]
    c1 = self.vector[0]*self.point[1] - self.vector[1]*self.point[0]
    
    a2 = line.vector[1]
    b2 = -line.vector[0]
    c2 = line.vector[0]*line.point[1] - line.vector[1]*line.point[0]

    d = a1*b2 - a2*b1
    if is_zero(d):
      return None 
    
    nx = b1*c2 - b2*c1
    ny = a2*c1 - c2*a1

    return [nx / d, ny / d]
    
class Segment:
  """A line segment. It is simply represented as two points. The points are arranged lexicographically.
  Currently only two dimensions are supported.
  """
  def __init__(self, p1, p2):
    assert(len(p1) == len(p2))
    index = 0
    if equals(p1[0], p2[0]):
      index = 1
    self.p1 = p1 if p1[index] < p2[index] else p2
    self.p2 = p2 if p1[index] < p2[index] else p1
  
  def line(self):
    return Line(self.p1, [self.p1[0] - self.p2[0], self.p1[1] - self.p2[1]])

  def contains_point(self, point):
    if len(point) != len(self.p1):
      return False
    for idx in range(len(self.p1)):
      mx = max(self.p1[idx], self.p2[idx])
      mn = min(self.p1[idx], self.p2[idx])
      p = point[idx]
      if (equals(p, mn) == False and p < mn) or (equals(p, mx) == False and point[idx] > mx):
        return False
    return True

  def intersects_one(self, segments):
    for segment in segments:
      if self.intersect(segment) != None:
        return True
    return False
  
  def intersect(self, segment):
    line1 = self.line()
    line2 = segment.line()

    pt = line1.intersect(line2)
    if pt == None:
      return None
    if self.contains_point(pt) and segment.contains_point(pt):
      return pt
    return None

class Polygon:
  """This is special polygon. It is represented by one long side and multiple shorter sides.
  We will call the longer side the [top] and the shorter sides the [bottom]. The idea is that
  they represent the bounds inside which a line may fall. If another line intersects the [top]
  and any one of the [bottom] segments then it necessarily intersects the line that this 
  polygon bounds.
  """
  def __init__(self, top, bottom):
    self.top = top
    self.bottom = bottom
  
  def intersects(self, polygon):
    """Checks whether this polygon and [polygon] intersect in such a way that the underlying
    line definitely intersects. That is on both [top] intersects with the other [top] and at
    least one of the other [bottom] and vice versa.

    Args:
        polygon (Polygon): The polygon to check for the desired intersection.
    """
    if not self.top.intersects(polygon.top):
      return False
    if not self.top.intersects_one(polygon.bottom):
      return False
    if not polygon.top.intersects_one(self.bottom):
      return False
    return True
    
### discriminant

class DiscriminantFunction:
  """This class wraps the functionality of evaluating the A-Discriminant for
  a given B matrix.
  """
  def __init__(self, b):
    """Initialize the dicriminant function.

    Args:
        b (List of integer lists): This is the transpose of thenullspace of 
        the A-hat matrix. It should be non-empty and all rows should have
        the same dimension.
    """
    self.b = b
    assert(len(b) > 0)
    l = len(b[0])
    self.dim = l
    for item in b:
      assert(len(item) == l)
  
  def evaluate(self, point):
    """Evaluates the function at the given point. The point should have the
    same dimension as the discriminant function.

    Args:
        point (List of double): point at which to evaluate the function.

    Returns:
        List of double: Returns None if the point is undefined (likely unbounded).
    """
    assert(len(point) == self.dim)
    value = [0]*self.dim
    for item in self.b:
      m = map(lambda idx: item[idx] * point[idx], range(self.dim))
      r = reduce(lambda x, y: x + y, m)
      if is_zero(r):
        return None
      l = log(abs(r))
      for idx in range(self.dim):
        value[idx] += item[idx] * l
    return value  

### 2d discriminant

def angle_to_point(angle):
  return [cos(angle), sin(angle)]

def angle_to_tangent(angle):
  return [-sin(angle), cos(angle)]

def point_to_angle(point):
  l = sqrt(point[0]*point[0] + point[1]*point[1])
  assert(not is_zero(l))
  return acos(point[0] / l)

def b_to_zero_angles(b):
  l = [0] + list(map(lambda bb: point_to_angle(bb), b))
  l.sort()
  return l

class Intersection:
  def __init__(self, r1, r2):
    self.r1 = r1
    self.r2 = r2

def find_nearest(f, v, bounds, depth):
  """Uses binary search to find the point that evaluates nearest to v.
  This makes a strong assumption on f. Namely, that it does not approach
  v and then go away and come back. This is a safe assumption for 2d
  A-discriminants, but unknown for higher dimensions. This could be made
  slightly faster by using a tolerance rather than the depth.

  Args:
      f (function): A function that evaluates the A-discriminant
      v (double or list of double): value to attempt to approach
      bounds (list): upper and lower bound to search
      depth (int): number of remaining iterations (bisections) to test

  Returns:
      double or list of double: returns the parameter that was found through binary search
  """
  m = lerp(bounds[0], bounds[1], 1, 2)
  if depth == 0:
    return m
  hv = f(bounds[1])
  lv = f(bounds[0])
  
  if distance_squared(hv, v) > distance_squared(lv, v):
    return find_nearest(f, v, [bounds[0], m], depth - 1)
  else:
    return find_nearest(f, v, [m, bounds[1]], depth - 1)

def lerp(lower, upper, step, steps):
  ''' Interpolates between [lower] and [upper]. Assuming there are [steps] number
  of steps between [lower] and [upper] it finds the [step]th step between. When 
  [step]==0 then lower is returned, when [step]==[steps] then [upper] is returned.

  Essentially returns:
    lower * (steps - step) / steps + upper * step / steps

  Args:
      lower (double or list of double): lower bound of the interpolation (value at [step]==0).
      upper (double or list of double): upper bound of the interpolation (value at [step]==[steps]).
      step (int): step number to produce.
      steps (int): number of steps.

  Returns:
      List of double: Returns None if the point is undefined (likely unbounded).
  '''
  interp = lambda l, u: u * step / steps + l * (steps - step) / steps
  if type(lower) == list:
    return list(map(lambda coords: interp(coords[0], coords[1]), zip(lower, upper)))
  return interp(lower, upper)

def simple_intersect(f, r1, r2, depth):
  size = 20
  bounds2 = [lerp(r2[0], r2[1], 2*size - 1, 2*size), lerp(r2[0], r2[1], 1, 2*size)]
  nearest_angle1 = None
  nearest_angle2 = None
  nearest_idx = None
  nearest_v = None
  delta = None
  for idx in range(1, size):
    x = lerp(r1[0], r1[1], idx, size)
    v = f(x)
    if abs(v[0]) > 10 or abs(v[1]) > 10:
      continue
    n = find_nearest(f, v, bounds2, 25)
    vn = f(n)
    ds = distance_squared(v, vn)
    if delta == None or ds < delta:
      nearest_angle1 = x
      nearest_angle2 = n
      nearest_v = vn
      delta = ds
      nearest_idx = idx
  if depth == 0:
    print('Near angles found: ', evalf((nearest_angle1, nearest_angle2)))
    print('Values are within this delta: ', evalf(delta))
    print('Value found: ', evalf(nearest_v))
    return (nearest_angle1, nearest_angle2, delta)
  lx = nearest_idx - 1
  hx = nearest_idx + 1
  lower = lerp(r1[0], r1[1], nearest_idx - 1, size)
  upper = lerp(r1[0], r1[1], nearest_idx + 1, size)
  return simple_intersect(f, [lower, upper], r2, depth - 1)

def intersect_line(line, point, vector):
  """Find the intersection of a [line] and a [vector] emanating from a given [point].
  If the vector is parallel to the line and the point is not on the line then there is
  no intersection and None is returned.

  Args:
      line (list of num): if line = sum_i a_i*x_i + c then line = [a_0, a_1,...,a_n, c]
      point (list of num): Point of form [p_0,...,p_n]
      vector (list of vector): Vector of form [v_0,...,v_n]

  Returns:
      list of num: The point of intersection, or None if it doesn't exist.
  """
  assert len(line) == (len(point) + 1), 'line must be 1 longer than point'
  assert len(point) == len(vector), 'point and vector must be same length'

  value = sum(map(lambda b: b[0] * b[1], zip(line, point))) + line[-1]
  if is_zero(value):
    return point

  # With a line given as ax + by + c == 0 and
  # line = [a, b, c]
  # With a point = [px, py] and vector = [vx, vy]
  # Then we have
  # a * (px + vx * n) + b * (py + vy * n) + c = 0
  # (a * vx + b * vy) * n = -c - a * px - b * py
  # n = - (c + a * px + b * py) / (a * vx + b * vy)
  # x = px + vx * n, y = py + vy * n
  
  numerator = - (line[-1] + sum(map(lambda b: b[0] * b[1], zip(line, point))))
  denominator = sum(map(lambda b: b[0] * b[1], zip(line, vector)))
  if is_zero(denominator):
    return None
  n = numerator / denominator
  return list(map(lambda b: b[0] + b[1] * n, zip(point, vector)))

def evaluate_line(line, point):
  """Evaluates the unknown coordinate of point. That coordinate should be None. That is, if

  line = [a, b, c] (ie a*x + b*y + c = 0)

  point = [1, None]

  Then it evaluates the line's y value at x = 1

  Args:
      line (list of num): The line to evalutate. If line is a*x + b*y + c = 0 then the input is [a,b,c]
      point (list of num): a list of points of length len(line) - 1 with one entry equal to None
  
  Returns:
      coordinates of the fully evaluated point.
  """
  assert len(line) == len(point) + 1, 'line must be one dimension larger than point'
  assert len(list(filter(lambda p: p == None, point))) == 1, 'should have 1 None argument on point'

  p = point + [1]
  null_index = None
  for idx in range(len(point)):
    if point[idx] == None:
      null_index = idx
  assert null_index != None, 'null index expected'
  if is_zero(line[null_index]):
    return None

  s = sum(map(lambda c, p: c * (p if p != None else 0), line, p))
  return - s / line[null_index]

def create_region(point, vector, lines):
  assert len(lines) >= 2, 'not enough lines for a region'

  p = point
  v = vector
  regions = []
  for line in lines:
    pp = intersect_line(line, p, v)
    regions.append([p, pp])
    p = pp
    v = vector_from_line(line)
  regions.append([p, point])
  return regions

def vector_from_line(line):
  return [-line[1], line[0]]

def create_arc(line):
  phi = atan2(-line[0], line[1])
  size = 100
  angles = map(lambda t: pi/2 * (t - size) / size, range(2*size + 1))
  pts = [(sin(theta)*cos(phi), sin(theta) * sin(phi), cos(theta)) for theta in angles]
  print(evalf(pts))
  return pts

### Tests

assert(lerp(0, 1, 50, 100) == 1/2)
assert(lerp(0, 1, 0, 100) == 0)
assert(lerp(0, 1, 100, 100) == 1)

assert(Line([0,0], [1,1]).intersect(Line([2,0], [1, -1])) == [1,1])
assert(Line([0,0], [1,1]).intersect(Line([2,0], [-1, -1])) == None)
# reverse the vector still get same results
assert(Line([0,0], [-1,-1]).intersect(Line([2,0], [1, -1])) == [1,1])

assert(Segment([0,0], [1,1]).intersect(Segment([3,0], [2, 1])) == None)
# check shared endpoint
assert(Segment([0,0], [1,1]).intersect(Segment([2,0], [1, 1])) == [1,1])
# check endpoint of just one
assert(Segment([0,0], [2,2]).intersect(Segment([2,0], [1, 1])) == [1,1])
# check interior point
assert(Segment([0,0], [2,2]).intersect(Segment([2,0], [0, 2])) == [1,1])

assert(distance_squared([1,2,3], [0,1,-1]) == 18)

assert(equals(point_to_angle([1,1]), pi / 4))

assert evaluate_line([1, 2, 3], [2, None]) == -5/2, 'bad y calcualation for x+2y+3 (x==2)'
assert evaluate_line([1, 2, 3], [None, 2]) == -7, 'bad x calcualation for x+2y+3 (y==2)'
assert evaluate_line([1, 0, 3], [None, 2]) == -3, 'bad x calcualation for x+3 (y==2)'
assert evaluate_line([0, 1, 2], [1, None]) == -2, 'bad 7 calcualation for y+2 (x==1)'

line = [1, 2, 3]
assert intersect_line(line, [1,1], [1,1]) == [-1, -1], 'incorrect line intersection'
assert intersect_line(line, [1,1], [1,2]) == [-1/5, -7/5], 'incorrect line intersection'
assert intersect_line(line, [1,4], [0,1]) == [1, -2], 'incorrect line intersection'
assert intersect_line(line, [-1/5,-7/5], [1,1]) == [-1/5, -7/5], 'incorrect line intersection'
assert intersect_line(line, [-1/5,-7/5], [-2,1]) == [-1/5, -7/5], 'vector is parallel but the point is on the line, should intersect'
assert intersect_line(line, [1,4], [-2,1]) == None, 'should have no intersection with parallel vector'

print(evalf([1,pi]))
print(evalf((1,pi)))

A = [[1,1,1,1], [0,1,2,3]]
NS = [[-1, 1, 1, -1], [1, -2, 1, 0]]
b = [[-1,1], [1,-2], [1,1], [-1,0]] # = NS^T

d = DiscriminantFunction(b)

f = lambda angle: d.evaluate(angle_to_point(evalf(angle)))
angles = b_to_zero_angles(b)

vals = simple_intersect(f, [angles[0], angles[1]], [angles[2], angles[3]], 3)
assert is_zero(vals[2] * 1e3), 'intersection not found'
assert equals(vals[0], 0.7338760438785756), 'incorrect left intersection angle'
assert equals(vals[1], 1.4082515450111763), 'incorrect right intersection angle'

vals = simple_intersect(f, [angles[0], angles[1]], [angles[3], angles[4]], 3)
assert(is_zero(vals[2]) == False)

A = [[0,1,2,3,4]]
AA = [[1,1,1,1,1],[0,1,2,3,4]]
NS = [[-1,1,0,1,-1],[0,1,-1,-1,1]]
b3 = [[1, 0, 0], [0, 1, 0], [0, 0, 1], [-4, -3, -2], [3, 2, 1]]

green = b3[-1]
blue = b3[-2]
yaxis = b3[0]
xaxis = b3[1]

pgreen = b3[-1]
pblue = b3[-2]
pyaxis = b3[0]
pxaxis = b3[1]
pzaxis = b3[2]

gl = Line3d(create_arc(green))
#bl = Line3d(create_arc(blue))
#yl = Line3d(create_arc(yaxis))
#xl = Line3d(create_arc(xaxis))
show(gl + bl + yl + xl)

region1 = create_region([-3, 0], [0, 1], [blue, xaxis])
region2 = create_region(region1[0][1], [0,1], [green, xaxis, blue])
region3 = create_region(region2[0][1], [1,0], [yaxis, xaxis, green])
region4 = create_region([0, 3], [1, -1], [xaxis, yaxis])

region5 = create_region([0, -3], [-1, 1], [xaxis, blue, yaxis])
region6 = create_region([-1/2, 0], vector_from_line(xaxis), [green, yaxis, blue])
region7 = create_region([0, 0], [0, -1], [green, xaxis])
region8 = create_region([3, 0], [0, -1], [blue, green, yaxis, xaxis])
region9 = create_region([0, -3], [1, 0], [green, blue, yaxis]) # this one is counter clockwise
region10 = create_region(region9[0][1], vector_from_line(green), [blue, [1, 0, 3]])

regions = [region1, region2, region3,
           region4, region5, region6,
           region7, region8, region9, region10]

for region in regions:
  print(region)


m = matrix([[1]*len(A[0])] + A)
Bm = m.transpose().integer_kernel().basis_matrix().transpose()
B = list(map(lambda b: list(b), list(Bm)))
print(B)
d = DiscriminantFunction(B)
f = lambda point: d.evaluate(point + [1])
print(f([-0.1, -0.25]))

point1 = [-0.2, 0]
point2 = intersect_line(b3[0], point1, [-2, 3])

point1 = [0, 0.4]
point2 = intersect_line(green, point1, [-1, 0])

point1 = [0, 0.6]
point2 = intersect_line(xaxis, point1, [-1, 1])

point1 = [0.5, 0]
point2 = [0, 0.5]

point1 = [0.5, 0]
point2 = [0, -0.5]

region11 = [-1, 0]
region12 = intersect_line(blue, region11, [1, 1])

region21 = [-0.5, 0]
region22 = intersect_line(green, region21, [-8, 3])

region31 = [0, 0.5]
region32 = intersect_line(green, region31, [-1, 0])

region41 = [0, 0.5]
region42 = [0.5, 0]

region51 = [-1, 0]
region52 = [0, -1]

region61 = [-0.5, 0]
region62 = [0, -0.5]

region71 = [-0.2, 0]
region72 = [0, -0.3]

region81 = [0, -0.5]
region82 = [0.5, 0]

region91 = [0, -0.6]
region92 = intersect_line(green, region91, [1, 0])

region101 = [0, -1.5]
region102 = intersect_line(blue, region101, [1, 0])


ppoint1 = [-0.7, 0]
ppoint2 = intersect_line(b3[0], ppoint1, [-2, 3])

ppoint1 = [-1, 0]
ppoint2 = [0, -1]

regions = [[region11, region12], [region21, region22], [region31, region32],
           [region41, region42], [region51, region52], [region61, region62],
           [region71, region72], [region81, region82], [region91, region92],
           [region101, region102]]

region1 = [[[-1,0], ]]

# 4, 9 within 0.09359803735962777

