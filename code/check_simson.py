import random, cmath, math
def foot(p,u,v):
    d=v-u; t=((p-u)*d.conjugate()).real/abs(d)**2; return u+t*d
def area2(x,y,z): return ((y-x)*(z-x).conjugate()).imag
random.seed(1); mx_on=0; mn_off=1e9
for _ in range(2000):
    o=complex(random.uniform(-3,3),random.uniform(-3,3)); r=random.uniform(.5,3)
    A,B,C,P=[o+r*cmath.exp(1j*random.uniform(0,2*math.pi)) for _ in range(4)]
    s=r*random.uniform(1.1,2)  # negative control: P off circle
    Q=o+s*cmath.exp(1j*random.uniform(0,2*math.pi))
    mx_on=max(mx_on,abs(area2(foot(P,B,C),foot(P,C,A),foot(P,A,B))))
    mn_off=min(mn_off,abs(area2(foot(Q,B,C),foot(Q,C,A),foot(Q,A,B)))/abs(area2(A,B,C)))
print("on-circle max |det| =",mx_on); print("off-circle min |det|/|ABC| =",mn_off)
