# FZZ parity Krein antiunitary critical eigenline (F11)

F11 proved/formalized. At every beta>0, canonical source-Krein operator A_beta anticommutes with canonical source-metric antiunitary J_beta. Positive-imaginary eigenvalue lambda satisfies -conj(lambda)=lambda, and J fixes its eigenline projectively.

Balanced eigenline coordinate y_beta=a_beta*(lambda_beta-p_beta)/q_beta, a=sqrt(r/p), has norm exactly 1. Define rho_beta=1/2+i arg(y_beta)/log 2. Then Re rho_beta=1/2, centered dyadic Mellin character chi(rho_beta)=y_beta, and source eigenvector v_beta=q_beta • w_beta(rho_beta), where w is F10 balanced carrier. Balanced crossing of rho_beta matches its reflection unconditionally.

This creates one literal source-derived critical dynamical mode per scale. Remaining gate is divisor incidence/surjectivity: every parity-Mellin zero must land in this family or in a richer infinite-dimensional operator, without importing zeta zeros.

Module: formal/GaloisForLFunctions/RHTower/FZZCigarParityKreinAntiunitaryCriticalEigenline.lean. Card: docs/drafts/pipeline/3-formalized/fzz-parity-krein-antiunitary-critical-eigenline.md. Wired umbrella. Direct Lean and targeted module build pass. Axioms only [propext, Classical.choice, Quot.sound]. Global lint has no issue in module; failures unrelated unreachable modules. Frontier map untouched.