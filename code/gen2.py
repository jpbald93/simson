from sympy import *
a1,a2,b1,b2,c1,c2,p1,p2,o1,o2,r=symbols('a1 a2 b1 b2 c1 c2 p1 p2 o1 o2 r')
S=a1*b2 - a1*c2 - a2*b1 + a2*c1 + b1*c2 - b2*c1
M=Matrix([[x,y,x**2+y**2,1] for x,y in [(a1,a2),(b1,b2),(c1,c2),(p1,p2)]])
K=expand(M.det())
def foot(p,u,v):
    d=(v[0]-u[0],v[1]-u[1]); N=(p[0]-u[0])*d[0]+(p[1]-u[1])*d[1]; D=d[0]**2+d[1]**2
    return (u[0]*D+N*d[0], u[1]*D+N*d[1], D)
A=(a1,a2);B=(b1,b2);C=(c1,c2);P=(p1,p2)
F=[foot(P,B,C),foot(P,C,A),foot(P,A,B)]
Q=expand(Matrix([list(f) for f in F]).det())
for s in [1,-1]:
    print(s, expand(Q - s*S**2*K)==0)
gs=[(x-o1)**2+(y-o2)**2-r**2 for x,y in [(a1,a2),(b1,b2),(c1,c2),(p1,p2)]]
# cofactor expansion along column 3: K = sum cof_i * (x_i^2+y_i^2); replace x^2+y^2 = g + 2o1x+2o2y + r^2-o^2
cof=[M.cofactor(i,2) for i in range(4)]
assert expand(K-sum(c*(M[i,2]) for i,c in enumerate(cof)))==0
assert expand(K-sum(c*gs[i] for i,c in enumerate(cof)))==0
print([str(factor(c)).replace('**','^') for c in cof])
