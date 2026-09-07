# CLG/TTF global source compensation and the mixed odd rank-three block

- **Stage:** 3-formalized
- **Result:** The canonical compensated literal-source determinant is strictly positive for every nonnegative center. The actual mixed odd rank-three determinant is strictly positive at every critical aperture.
- **Scope:** Finite signed section through derivative ten. The complete signed Hankel hierarchy, hence RH, remains unproved.
- **Capstone:** `ThetaCuspGlobalOddCompensation.lean`.

## Exact statement

Let `Φ` be the literal full theta source, `φ` its first atom, `T` its first two atoms, and `q=π exp(2x)`. Write

`j_n=D_t^n[Φ(x+t)Φ(x−t)]|_(t=0)`,

`A=−j₂`, `B=j₄`, `C=−j₆`, `D=j₈`, `E=−j₁₀`,

`Δ=AC−B²`, `H=ACE−AD²−B²E+2BCD−C³`,

`G=3Φ²+2xΦΦ′`, `H_K=H+KΔG`.

Lean proves `H_K(x)>0` for every `x≥0` and every `10⁹≤K≤3·10⁹`. The exact canonical coefficient `K_*=−H(0)/(Δ(0)Φ(0)²)` lies strictly inside this interval, so it satisfies the same global conclusion without any source-sign premise.

For every `0<a<1/2`, the actual center-mixed density `f_a` satisfies

`det Hankel₃(−f_a''(0),f_a⁽⁴⁾(0),−f_a⁽⁶⁾(0),f_a⁽⁸⁾(0),−f_a⁽¹⁰⁾(0))>0`.

The integral-preserving correction and its receiver are proved in the existing corpus. The new global source sign discharges their remaining input.

## Retained model and exact reserves

Normalize each even reflection jet by `φ²q^k`, retaining sign `(-1)^k`. The literal two-atom entries have the exact form

`A_k=N_k(q,z)/(q^(k−1)(2q−3)²)`, `z=exp(−3q)`, `1≤k≤5`.

`TwoAtomOddAlgebra` records every numerator, the determinant numerator and the leading-minor numerator. `ThetaCuspTwoAtomOddProfiles` proves their incidence with the actual two atoms using the literal derivative recurrence through order ten. Denominators are positive on the required interval.

For `37/10≤q≤5`, exponential Taylor bounds give

`65000[1+3(q−37/10)+(9/2)(q−37/10)²] z≤1`.

For `5≤q≤7`, `z≤1/3000000`. These admissions use proved rational bounds on `exp(1)` and elementary exponential identities. They have no sampled or numerical source premise.

After clearing the positive denominators, explicit nonnegative Bernstein expansions prove:

- `H_two/(φ⁶q⁹)≥15·10⁹` on `[37/10,5]`;
- `H_two/(φ⁶q⁹)≥85·10⁹` on `[5,7]`;
- `Δ_two/(φ⁴q⁴)≤33000` on `[5,7]`.

The lower-middle determinant uses the coupled envelope variable `v=65000[1+3(q−37/10)+(9/2)(q−37/10)²]z`, rather than replacing the exponential by an independent constant. The polynomial identities and all coefficient signs are kernel-checked symbolic algebra.

On the static box `37/10≤q≤7`, `0≤z≤1/65000`, the retained entries lie in

`[8,11]`, `[180,310]`, `[100,14000]`, `[1000,800000]`, `[10⁶,55·10⁶]`,

and `0≤A₁A₃−A₂²≤55000`. The same bounds at `z=0` control the exact first-atom entries. Three separate entry modules keep the checks bounded in memory.

## Complete infinite-source error

Set `B=q−3/2` and `δ=exp(−8(q−49/20))/1000000`. The existing deep-tail theorem gives

`|E_deep⁽ⁿ⁾|≤(16q)^nδ`, `n≤10`, `q≥37/10`.

For the second-atom tilted spectral moments, the all-order exact profile is

`M_second(B,n)=exp(−9/2) exp(−3B) N_n(B)/B^(n+1)`,

where `N₀=18+16B` and `N_(n+1)=(3B+n+1)N_n−B N_n′`. Differentiation proves this identity at every order. The order-ten endpoint has `N₁₀(2)=27163123200`; the symbolic exponential lower bound `exp(21/2)≥30000` gives

`M_second(2,10)≤3^10/100`.

Support `t≥3` gives `(t/3)^n≤(t/3)^10` for `n≤10`. Monotonicity in the tilt then proves `M_second(B,n)≤3^n/100` for all `B≥2`. Adding the complete deep measure yields

`M_higher(B,n)≤3^n/100+8^nδ`.

The exact scalar cooling score satisfies `|L_(n,0)(z)|≤(2z)^n` for `n≤10`, `z≥111/10`, by explicit positive polynomial expansions. Integration against the complete measure, whose support gives `qt≥111/10`, proves

`|R⁽ⁿ⁾|≤(6q)^n/100+(16q)^nδ`, where `R=Φ/φ−1`.

The retained partition is exactly `A=T/φ=1+R−E_deep`. Hence

`|A⁽ⁿ⁾|≤0^n+(6q)^n/100+2(16q)^nδ`.

The convention `0^0=1` retains the constant only at order zero. The exact reflected error is

`V=A_+E_−+E_+A_−+E_+E_−`.

The binomial theorem collapses its complete derivative majorant to

`|V⁽ⁿ⁾|≤2(16q)^nδ+(22q)^nδ/50+5(32q)^nδ²`.

No cross term or quadratic remainder is discarded. The full reflected source error remains the convolution of these bounds with the exact reflected first-atom jets; odd first-atom jets vanish before estimation.

For `k≤5`, monotonicity of `q^k exp(−8q)` and `exp(10)≥21000` give

`q^kδ≤(37/10)^k/(21·10⁹)`,

`q^kδ²≤(37/10)^k/(21·10⁹)²`.

The resulting five normalized complete-to-two-atom errors are at most

`(10⁻⁶,10⁻³,1,200,175000)`.

These are theorems about the complete literal source over the whole interval, not assumed approximation tolerances.

## Determinant transfer and global closure

The determinant perturbation retains the exact leading minor as the coefficient of the fifth-entry error. Telescoping the other four entries and using the stated positive boxes gives a total error at most `14.5·10⁹`. The upper-middle full leading minor remains positive and at most `33100`.

Consequently:

- On `[37/10,5]`, `H/(φ⁶q⁹)≥0.5·10⁹`. The existing source theorem gives `G≥Φ²/2>0`, so every `K≥0` preserves strict positivity.
- On `[5,7]`, `H/(φ⁶q⁹)≥70.5·10⁹`, `0<Δ/(φ⁴q⁴)≤33100`, and `G/(φ²q⁵)≥−1/2500`. Thus for `0≤K≤3·10⁹`, the adverse correction costs at most `39.72·10⁹`. Lean records the lower reserve `H_K/(φ⁶q⁹)≥30·10⁹`.

The existing energy argument covers `0≤x≤8/95` for `K≥10⁹`. For larger centers, `q≥37/10`; the middle result applies until `q=7`, where the existing complete tail result applies. These regions cover every nonnegative center exactly.

The weighted corrected determinant is at least `[r sinh(ar)]³H_K(r/2)`. Its correction has proved zero half-line integral and leaves the actual mixed tenth entry unchanged. Applying the existing positive-matrix integral theorem proves the stated strict mixed odd determinant for every critical aperture.

## Lean verification and remaining work

Twenty-four new modules, 3733 lines and 100 public declarations were checked individually with foreground `lake env lean` calls. Required oleans only; no full, umbrella or dependency-cascade build. New imports are wired into `HTGeometry.lean` and `RHTower.lean`.

A scratch axiom audit of the new global canonical theorem, mixed determinant theorem, all-order second-atom formula, fifth-entry error and upper-middle compensated reserve reports only `propext`, `Classical.choice`, `Quot.sound`. `scripts/formal_tools.py lint` passes; its warnings concern existing large files.

The [full six-dimensional signed matrix and arbitrary six-point cluster assembly](clg-ttf-sixth-rank-and-successor-source.md) are also formalized. The next source comparison is the explicit rank-seven successor integral; no propagation law for all orders is proved. The exact all-order signed source cone is RH-equivalent; this finite result does not establish RH.
