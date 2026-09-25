"""Mechanical proof-format experiment; exact identities still require Lean checking."""
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction
from math import gcd
from pathlib import Path
import json
import re

words=['Zero','One','Two','Three','Four','Five','Six']

def balanced_annotations(s):
    s=re.sub(r'\^(\d+)',r'^(\1 : ℕ)',s)
    out='';stack=[]
    for c in s:
        if c=='(': stack.append(len(out));out+=c
        elif c==')':
            k=stack.pop()
            # Original Six is already annotated at each sum node.
            part=out[k:]
            if '+\n' in part and not part.rstrip().endswith(': ℝ'): out+=' : ℝ'
            out+=c
        else: out+=c
    return out

def one(word):
    module='PolynomialODEEvenCompactMoment'+word
    name='evenCompactUnitMoment'+word
    s=Path(module+'.lean').read_text()
    body=re.split(r'def '+name+r' \(r t _?v : ℝ\) : ℝ :=\n',s)[1].split('\n\n/--')[0]
    pats=r'\((-?\d+)(?:/(\d+))? : ℝ\)'
    cs=[Fraction(int(m[1]),int(m[2] or '1')) for m in re.finditer(pats,body)]
    denominator=1
    for c in cs: denominator=denominator*c.denominator//gcd(denominator,c.denominator)
    def replace(m):
        c=Fraction(int(m[1]),int(m[2] or '1'))*denominator
        assert c.denominator==1
        return '('+str(c.numerator)+' : ℝ)'
    body=re.sub(pats,replace,body)
    body=balanced_annotations(body)
    newmodule=module+'Integer'
    text=f'''import GaloisForLFunctions.HTGeometry.{module}

/-! # Exact integer numerator for compact even moment {word.lower()} -/
namespace HTGeometry
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

/-- One positive common denominator separates scalar arithmetic from polynomial expansion. -/
def {name}Numerator (r t v : ℝ) : ℝ :=
{body}

/-- Exact symbolic equality with the previously proved normalized source moment. -/
theorem {name}_eq_numerator (r t v : ℝ) :
    {name} r t v = {name}Numerator r t v / ({denominator} : ℝ) := by
  unfold {name} {name}Numerator
  ring

end
end HTGeometry
'''
    if word=='Zero': text=text.replace('Numerator (r t v : ℝ)', 'Numerator (r t _v : ℝ)')
    Path('output',newmodule+'.lean').write_text(text)
    return {'word':word,'denominator':denominator,'terms':len(cs)}

if __name__=='__main__':
    Path('output').mkdir(exist_ok=True)
    with ProcessPoolExecutor(max_workers=7) as pool: rows=list(pool.map(one,words))
    Path('output/metadata.json').write_text(json.dumps(rows,indent=2)+'\n')
    print(json.dumps(rows),flush=True)
