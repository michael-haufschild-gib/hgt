"""Render saved arithmetic-averaging results on the authorized Runpod only."""
import os
os.environ['OPENBLAS_NUM_THREADS'] = '4'
import json
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

root = Path(__file__).resolve().parent
power = json.loads((root/'validation.json').read_text())
refined = json.loads((root/'refined_results.json').read_text())
sizes = [r['N'] for r in power]
colors = ['#3b82f6', '#22a68b', '#b06ddd', '#d27831']
plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 10,
                     'axes.spines.top': False, 'axes.spines.right': False})
fig, axes = plt.subplots(1, 3, figsize=(15, 4.5), layout='constrained')
axes[0].loglog(sizes, [r['power']['l2_norm'] for r in power], 'o-',
               color='#b74f55', label='Best power damping found')
axes[0].loglog(sizes, [r['validation_norm'] for r in refined['validation']], 'o-',
               color='#3b82f6', label='Positive cutoff averages')
axes[0].set(xlabel='Maximum cutoff N', ylabel='Measured full L² error',
            title='Finite feasible vectors')
axes[0].legend(fontsize=9, loc='center right')
axes[0].grid(alpha=.15)
for n, color in zip(sizes, colors):
    alpha = np.load(root/('refined_%d.npz' % n))['alpha']
    weights = np.cumsum(alpha[::-1])[::-1]
    k = np.arange(1, n+1)
    axes[1].semilogx(k, weights, color=color, label='N=%d' % n)
    active = alpha > 0
    axes[2].scatter(k[active], alpha[active], s=15, color=color, label='N=%d' % n)
axes[1].set(xlabel='Coefficient index k', ylabel='w(k)', ylim=(-.03, 1.03),
            title='Coefficients a(k) = μ(k) w(k)')
axes[1].legend(fontsize=9)
axes[2].set(xscale='log', yscale='log', xlabel='Selected raw cutoff',
            ylabel='Positive averaging mass', title='Sparse cutoff distributions')
axes[2].legend(fontsize=9)
fig.suptitle('Arithmetic averaging: numerical evidence, no convergence certificate', fontsize=13)
fig.savefig(root/'arithmetic-averaging.png', dpi=180)
fig.savefig(root/'arithmetic-averaging.pdf')
