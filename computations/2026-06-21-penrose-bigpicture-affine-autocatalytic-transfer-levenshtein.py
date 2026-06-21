node = 'autocatalytic rate law: conserved total pool M is a bulk passport; after fixing M, the log ratio log(x/a) evolves linearly and carries kinetic shape beyond the pool'
transfers = {
    'passport_subtracted_shape': 'affine observables factor through finite passport Pi; subtract the passport and test transverse seam shape rather than total count or sum',
    'log_ratio_transport': 'replace scalar amplitude by log transport ratio of two coupled source reservoirs and test whether its slope survives affine gauges',
    'central_moment_tower': 'use all central moments after fixing total mass and barycenter, because low-order affine summaries are blind to distribution shape'
}

def lev(a,b):
    a=a.lower(); b=b.lower()
    prev=list(range(len(b)+1))
    for i,ca in enumerate(a,1):
        cur=[i]
        for j,cb in enumerate(b,1):
            cur.append(min(prev[j]+1, cur[j-1]+1, prev[j-1]+(ca!=cb)))
        prev=cur
    return prev[-1]
for name,text in transfers.items():
    print(f"{name}: {lev(node,text)}")
