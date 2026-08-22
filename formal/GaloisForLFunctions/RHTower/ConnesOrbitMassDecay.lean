import GaloisForLFunctions.RHTower.ConnesBoxMajorant

/-!
# §VII (50) and the conclusion of Lemma 2

§VII (49)-(50) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

Lemma 2 asserts that the error terms `δ_q(Λ)` of (35) are summable over the `S`-unit group, with
sum `σ(Λ) = O(Λ^{-N})` for every `N`.  Connes reaches it by combining

* (49), `|F̄(ε_Λ ξ̂)(x)| Sup_S|x_v|^α ≤ δ_Λ` with `δ_Λ = O(Λ^{-N})` — the output of (41) and (42),
  which are Lean-closed at the archimedean place;
* (36), `Sup_S |q_v| ≥ exp(d(q,1))` for a word metric `d` on `O_S^*` — Lean-closed as
  `ConnesSUnitSupBound` (A4);
* the geometric convergence of `∑_{O_S^*} exp(-d(q,1))`, Lean-closed as
  `ConnesOrbitGeometricConvergence.connes_summable_exp_neg_latticeL1`.

What remains is the bookkeeping that turns a per-orbit bound `|δ_q| ≤ D · exp(-c d(q,1))` into a
bound on the total mass, and the transfer of rapid decay from `D(Λ)` to `σ(Λ)`.  Both are proved
here, over the lattice `ℤ^d` in which the `S`-unit group embeds with finite kernel.
-/

open Filter Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- **§VII (50), the total mass.**  A family bounded orbit-wise by `D·exp(-c d(q,1))` has total
mass at most `D` times the geometric constant. -/
theorem connes_orbitMass_le {d : ℕ} (hd : 0 < d) {c : ℝ} (hc : 0 < c)
    {δ : (Fin d → ℤ) → ℝ} {D : ℝ}
    (hδ : ∀ ν, |δ ν| ≤ D * Real.exp (-(c * (_root_.RHTower.latticeL1 ν : ℝ)))) :
    (∑' ν : (Fin d → ℤ), |δ ν|)
      ≤ D * ∑' ν : (Fin d → ℤ), Real.exp (-(c * (_root_.RHTower.latticeL1 ν : ℝ))) := by
  have hgeo : Summable fun ν : Fin d → ℤ =>
      Real.exp (-(c * (_root_.RHTower.latticeL1 ν : ℝ))) :=
    connes_summable_exp_neg_latticeL1 hd hc
  have hmaj : Summable fun ν : Fin d → ℤ =>
      D * Real.exp (-(c * (_root_.RHTower.latticeL1 ν : ℝ))) := hgeo.mul_left D
  have habs : Summable fun ν : Fin d → ℤ => |δ ν| := by
    refine hmaj.of_nonneg_of_le (fun ν => abs_nonneg _) hδ
  calc (∑' ν : (Fin d → ℤ), |δ ν|)
      ≤ ∑' ν : (Fin d → ℤ), D * Real.exp (-(c * (_root_.RHTower.latticeL1 ν : ℝ))) :=
        habs.tsum_le_tsum hδ hmaj
    _ = D * ∑' ν : (Fin d → ℤ), Real.exp (-(c * (_root_.RHTower.latticeL1 ν : ℝ))) :=
        tsum_mul_left

/-- The total mass is nonnegative. -/
theorem connes_orbitMass_nonneg {d : ℕ} {δ : (Fin d → ℤ) → ℝ} :
    0 ≤ ∑' ν : (Fin d → ℤ), |δ ν| :=
  tsum_nonneg fun _ => abs_nonneg _

/-- **§VII Lemma 2, the conclusion.**  If the orbit-wise bound decays faster than every power of
the cutoff, so does the total mass. -/
theorem connes_orbitMass_rapidDecay {d : ℕ} (hd : 0 < d) {c : ℝ} (hc : 0 < c)
    {δ : ℝ → (Fin d → ℤ) → ℝ} {D : ℝ → ℝ}
    (hδ : ∀ (L : ℝ) (ν : Fin d → ℤ),
      |δ L ν| ≤ D L * Real.exp (-(c * (_root_.RHTower.latticeL1 ν : ℝ))))
    (N : ℕ) (hlim : Tendsto (fun L : ℝ => L ^ N * D L) atTop (𝓝 0)) :
    Tendsto (fun L : ℝ => L ^ N * ∑' ν : (Fin d → ℤ), |δ L ν|) atTop (𝓝 0) := by
  set K : ℝ := ∑' ν : (Fin d → ℤ), Real.exp (-(c * (_root_.RHTower.latticeL1 ν : ℝ))) with hK
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact tsum_nonneg fun ν => (Real.exp_pos _).le
  have hlimK : Tendsto (fun L : ℝ => (L ^ N * D L) * K) atTop (𝓝 0) := by
    simpa using hlim.mul_const K
  refine squeeze_zero' ?_ ?_ hlimK
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    exact mul_nonneg (by positivity) connes_orbitMass_nonneg
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    have hmass := connes_orbitMass_le hd hc (hδ L)
    have hLN : (0 : ℝ) ≤ L ^ N := by positivity
    calc L ^ N * ∑' ν : (Fin d → ℤ), |δ L ν|
        ≤ L ^ N * (D L * K) := mul_le_mul_of_nonneg_left hmass hLN
      _ = (L ^ N * D L) * K := by ring

end

end GaloisForLFunctions.RHTower
