"""Render archived K-test results on Runpod; no new optimization."""
import pathlib, json
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
ROOT=pathlib.Path(__file__).resolve().parent
data=json.loads((ROOT/'results.json').read_text())
fig,axs=plt.subplots(1,2,figsize=(11.2,4.1),layout='constrained')
rows=[]
for case in data['cases']:
    rs=case['results']; n=case['N']; m=[r['m'] for r in rs]
    axs[0].semilogy(m,[r['norm'] for r in rs],'-o',label='N = %d'%n,markersize=4)
    axs[1].semilogy(m,[r['tail_max_abs_coefficient'] for r in rs],'-o',label='N = %d'%n,markersize=4)
    best=min(rs,key=lambda r:r['norm'])
    unit=[r for r in rs if r['max_abs_coefficient']<=1]
    best_unit=min(unit,key=lambda r:r['norm'])
    for r in [best,best_unit]:
        fraction=r['region_energies_t_lt_1N__to_1M__to_1__above_1'][0]/r['norm']**2
        r['fraction_energy_t_lt_1N']=fraction
    rows.append({'N':n,'best':best,'best_unit':best_unit})
axs[0].set(ylabel='Full residual L² norm',xlabel='Matched odd moments m',title='More matched moments need not reduce full error')
axs[1].set(ylabel='Maximum absolute tail coefficient',xlabel='Matched odd moments m',title='Coefficient cost of exact moment interpolation')
axs[1].axhline(1,color='#8b2635',linestyle='--',linewidth=1,label='Unit budget')
for ax in axs:
    ax.grid(alpha=.2);ax.legend(frameon=False);ax.set_xticks(range(9))
fig.savefig(ROOT/'boundary-moments.png',dpi=180)
fig.savefig(ROOT/'boundary-moments.pdf')
allrows=[r for c in data['cases'] for r in c['results']]
summary={'cases':rows,'max_quadrature_norm_difference':max(abs(r['norm']-r['training_norm']) for r in allrows),
    'max_mp100_residual_difference':max(r['max_mp100_residual_difference'] for r in allrows),
    'max_float_scaled_moment_defect':max(r['float_scaled_moment_defect'] for r in allrows),
    'max_left_tail_energy_bound':max(r['left_tail_energy_bound'] for r in allrows),
    'all_heads_exact':all(r['head_exact'] for r in allrows),'seconds':data['seconds']}
(ROOT/'summary.json').write_text(json.dumps(summary,indent=2))
table=['| N | Best m | Full norm | Coefficient bound | Best m within unit box | Unit-box norm |',
       '|---:|---:|---:|---:|---:|---:|']
for z in rows:
    b,u=z['best'],z['best_unit']
    table.append('| %d | %d | %.9g | %.9g | %d | %.9g |'%(z['N'],b['m'],b['norm'],b['max_abs_coefficient'],u['m'],u['norm']))
report='''# Exact boundary-moment repair: finite experiment

Exploratory numerical data, not a proof or a certified continuum bound.
The frozen K-test and its mathematical constraints are in
`../../../1-in-progress/chronological-boundary-moment-repair.md`.

At N=512,2048,8192, freeze the first N/2 coefficients to Möbius. For each
m=0,…,8, impose exact harmonic charge zero, coefficient sum −2, and the first
m odd Taylor cancellation moments. Select the unique tail with minimum sum
of squared coefficients. There is no full-residual optimization or clipping.

## Results

'''+ '\n'.join(table)+'''

At N=512, moving from m=3 to m=8 raises the full error from 4.04774603e−6
to 1.59427516e−5 and the coefficient bound from 1 to 10.2558158. At N=8192,
all nine cases retain the unit bound; the best is m=5, error 5.20263969e−7.
Neither norm nor budget behavior in m can be extrapolated to every cutoff.
The frozen qualitative prediction of a coefficient/error tradeoff appears
in these cases; this is not an asymptotic obstruction.

The error below t=1/N is already tiny at the best moment orders. The full
error is concentrated outside that Taylor-scale interval. Exact derivatives
and harmonic charge therefore do not settle the missing approaching-zero
remainder. `summary.json` gives the regional fractions for each selected case.

## Numerical audit and limitations

The moment Gram systems and tail coordinates use 100 decimal digits. All
27 systems solved. High-precision scaled moment residuals range from about
1e−101 to 1e−93. Floats saved in CSV are separately checked against every
scaled moment; those residuals include rounding of the coefficients.

Training uses composite Gauss–Legendre order 24 in log t. Validation uses
order 60 on shifted, narrower log intervals, without reusing training nodes.
Both cover the near-zero endpoint; the omitted left energy is bounded using
the actual coefficient maximum. At t≥80, the algebraic charge contribution
S²/80 is included exactly for the saved float vector. The remaining tail norm
is bounded by [1+C/(1−exp(−80))²]exp(−80)/sqrt(2), with C the actual budget.
Four actual residual evaluations per vector, at Nt=.01,1,10,100, are recomputed
with 100 digits. These are checks, not rigorous quadrature error intervals.

'''
report+='Maximum independent quadrature norm difference: %.4g.\n\n'%summary['max_quadrature_norm_difference']
report+='Maximum high-precision residual spot difference: %.4g.\n\n'%summary['max_mp100_residual_difference']
report+='Maximum saved-float scaled moment defect: %.4g.\n\n'%summary['max_float_scaled_moment_defect']
report+='Largest omitted-left energy bound: %.4g.\n\n'%summary['max_left_tail_energy_bound']
report+='''## Reproduction and files

All mathematical computation ran on authorized Runpod
`root@157.157.221.29:27094`, directory
`/root/chronological-boundary-moments-20260906`.
Three worker processes, four BLAS threads each. Python 3.8.10, NumPy 1.24.4,
SciPy 1.10.1, mpmath 1.3.0. Run `python3 moments.py` in that directory.
It imports `kernel_reference.py` from sibling
`/root/chronological-arithmetic-averaging-20260906`; that helper is also
archived locally under the corresponding earlier computation folder.
Plotting uses Matplotlib from
`PYTHONPATH=/root/chronological-bounded-repair-20260906/deps python3 summarize.py`.

`results.json` and per-N JSON: all moment coordinates, diagnostics and timings.
`coeff_N_m.csv`: every actual saved coefficient and its Möbius reference.
`vectors_N.npz`: all vectors and weighted validation residuals.
`run.log`: raw output. `summary.json`: selected cases and aggregate checks.
`boundary-moments.png/.pdf`: plots of full error and tail coefficient cost.

No zero ordinates were supplied to the construction. No numerical result is
used in Lean. The fixed-dimensional obstruction and growing-jet source have
separate paper proofs; these data establish neither of those theorems nor RH.
'''
report+='\nTotal computation and validation time: %.3f seconds.\n'%data['seconds']
(ROOT/'REPORT.md').write_text(report)
print(json.dumps({k:v for k,v in summary.items() if k!='cases'},indent=2))
