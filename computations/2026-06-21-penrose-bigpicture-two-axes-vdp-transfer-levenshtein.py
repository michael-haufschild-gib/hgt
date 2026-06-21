node = 'negative resistance oscillator: same realized circuit equation, but stability comes from amplitude-dependent sign-changing energy balance and averaged limit-cycle radius'
transfers = {
    'realization_not_positivity': 'functional equation or weld realization can hold while positivity/localization fails; the sign-changing quadratic form is the separate RH axis',
    'source_built_energy_balance': 'construct a source-built energy form whose sign balance forces kappa minus zero without reading zero locations',
    'passport_subtracted_gain': 'subtract affine passport volume to expose transverse gain/loss shape beyond measured amplitude'
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
