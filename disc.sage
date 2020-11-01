from sage.ext.fast_eval import fast_float_constant

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
  m = (bounds[0] + bounds[1]) / 2
  if depth == 0:
    return m
  hv = f(bounds[1])
  lv = f(bounds[0])
  
  if distance_squared(hv, v) > distance_squared(lv, v):
    return find_nearest(f, v, [bounds[0], m], depth - 1)
  else:
    return find_nearest(f, v, [m, bounds[1]], depth - 1)

def lerp(lower, upper, step, steps):
  interp = lambda l, u: u * step / steps + l * (steps - step) / steps
  if type(lower) == list:
    return list(map(lambda coords: interp(coords[0], coords[1]), zip(lower, upper)))
  return interp(lower, upper)

def simple_intersect(f, r1, r2, depth):
  size = 20
  bounds2 = [r2[0] * (size - 1) / size + r2[1] * 1 / size, r2[0] * 1 / size + r2[1] * (size - 1) / size]
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

print(evalf([1,pi]))
print(evalf((1,pi)))

A = [[1,1,1,1], [0,1,2,3]]
NS = [[-1, 1, 1, -1], [1, -2, 1, 0]]
b = [[-1,1], [1,-2], [1,1], [-1,0]] # = NS^T

d = DiscriminantFunction(b)

f = lambda angle: d.evaluate(angle_to_point(fast_float_constant(angle)()))
angles = b_to_zero_angles(b)

vals = simple_intersect(f, [angles[0], angles[1]], [angles[2], angles[3]], 3)
assert equals(vals[2], 0), 'intersection not found'
assert equals(vals[0], 0.7338760438785756), 'incorrect left intersection angle'
assert equals(vals[1], 1.4082515450111763), 'incorrect right intersection angle'

vals = simple_intersect(f, [angles[0], angles[1]], [angles[3], angles[4]], 3)
assert(equals(vals[2], 0) == False)

AA = [[1,1,1,1,1],[0,1,2,3,4]]
NS = [[-1,1,0,1,-1],[0,1,-1,-1,1]]
b3 = [[1, 0, 0], [0, 1, 0], [0, 0, 1], [-4, -3, -2], [3, 2, 1]]

m = matrix(AA)
# m.transpose().null_space()

Bm = m.transpose().integer_kernel().basis_matrix().transpose()
B = map(lambda b: list(b), list(Bm))
print(list(B))