import GaloisForLFunctions.HTGeometry.FastForwardableStratumCodimension

/-!
# Incubation transport: uniform-in-time tubes, seed selection, and edge coupling

A synthesis certificate carried by one Hamiltonian transports to every Hamiltonian within
`(eps - eta)/L` of it in operator norm, uniformly over the whole time window `[0,L]`: Duhamel's
bound costs `t‖H-K‖`, which the window length controls once and for all.

A finite seed family whose good set has pointwise density `1-beta` in the seeds has one seed whose
good set has measure at least `1-beta`: averaging the indicator over the seeds and integrating gives
the selection, with no measurability requirement beyond that of the individual good sets.

Finally a coefficient shell built from unit-norm generators is Lipschitz with constant the square
root of the number of generators, and a centre whose edge coefficient is bounded below keeps half of
that coupling throughout a tube of half that radius.
-/

open MeasureTheory Metric Set
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

open _root_.HTGeometry

noncomputable section

/-! ## Uniform-in-time Duhamel transport -/

section Transport

variable {d : Type*} [Fintype d] [DecidableEq d] {Γ : Type*}

/-- **`(11)`: the certificate transports across the whole window.**  If a carrier Hamiltonian has a
`B`-gate certificate at slack `eta` at every time, then every Hamiltonian whose distance to it costs
at most `epsMinus - eta` over the window has the same certificate at slack `epsMinus`, uniformly for
`0 ≤ t ≤ L`. -/
theorem approxComplexity_orbitState_le_of_window
    (act : Γ → EuclideanSpace ℂ d → EuclideanSpace ℂ d) (chi : EuclideanSpace ℂ d)
    {Hx Hy : Matrix d d ℂ} (hHx : IsSelfAdjoint Hx) (hHy : IsSelfAdjoint Hy)
    {ψ : EuclideanSpace ℂ d} (hψ : ‖ψ‖ = 1) {eta epsMinus L : ℝ} {B : ℕ}
    (hcert : ∀ s : ℝ, ∃ w : List Γ, w.length ≤ B ∧
      dist (orbitState Hy ψ s) (wordAct act w chi) ≤ eta)
    (hgap : L * ‖Hx - Hy‖ ≤ epsMinus - eta)
    {t : ℝ} (ht0 : 0 ≤ t) (htL : t ≤ L) :
    approxComplexity act chi epsMinus (orbitState Hx ψ t) ≤ B := by
  have hmove : dist (orbitState Hx ψ t) (orbitState Hy ψ t) ≤ epsMinus - eta := by
    refine le_trans (dist_orbitState_le hHx hHy ψ hψ t) ?_
    have habs : |t| = t := abs_of_nonneg ht0
    rw [habs]
    exact le_trans (mul_le_mul_of_nonneg_right htL (norm_nonneg _)) hgap
  obtain ⟨w, hw, hd⟩ :=
    exists_witness_of_dist_le (act := act) (chi := chi) hmove (hcert t)
  refine approxComplexity_le_of_witness act chi w hw ?_
  linarith

end Transport

/-! ## Finite seed selection -/

section Selection

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
variable {Q : Type*} [Fintype Q]

/-- Averaging a pointwise seed-density bound over the space. -/
theorem sum_measureReal_ge_of_pointwise (A : Q → Set Ω) (hmeas : ∀ q, MeasurableSet (A q))
    {c : ℝ} (hpt : ∀ x, c ≤ ∑ q, Set.indicator (A q) (1 : Ω → ℝ) x) :
    c * μ.real Set.univ ≤ ∑ q, μ.real (A q) := by
  classical
  have hint : ∀ q ∈ (Finset.univ : Finset Q),
      Integrable (Set.indicator (A q) (1 : Ω → ℝ)) μ :=
    fun q _ => (integrable_const (1 : ℝ)).indicator (hmeas q)
  have hsum : Integrable (fun x => ∑ q, Set.indicator (A q) (1 : Ω → ℝ) x) μ :=
    integrable_finsetSum _ hint
  have hmono : ∫ _x : Ω, c ∂μ ≤ ∫ x, ∑ q, Set.indicator (A q) (1 : Ω → ℝ) x ∂μ :=
    integral_mono (integrable_const c) hsum hpt
  rw [integral_const, smul_eq_mul] at hmono
  rw [integral_finsetSum _ hint] at hmono
  have hval : ∀ q, ∫ x, Set.indicator (A q) (1 : Ω → ℝ) x ∂μ = μ.real (A q) :=
    fun q => integral_indicator_one (hmeas q)
  rw [Finset.sum_congr rfl fun q _ => hval q] at hmono
  calc c * μ.real Set.univ = μ.real Set.univ * c := by ring
    _ ≤ ∑ q, μ.real (A q) := hmono

omit [IsFiniteMeasure μ] in
/-- **Finite Fubini seed selection.**  If the seed indicators sum to at least `card Q` times the
target density, one seed attains that density. -/
theorem exists_measureReal_ge [Nonempty Q] (A : Q → Set Ω) {c : ℝ}
    (h : (Fintype.card Q : ℝ) * c ≤ ∑ q, μ.real (A q)) :
    ∃ q, c ≤ μ.real (A q) := by
  classical
  by_contra hcon
  push Not at hcon
  have hlt : ∑ q, μ.real (A q) < ∑ _q : Q, c :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun q _ => hcon q
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hlt
  have : (Fintype.card Q : ℝ) * c < (Fintype.card Q : ℝ) * c := by
    calc (Fintype.card Q : ℝ) * c ≤ ∑ q, μ.real (A q) := h
      _ < (Fintype.card Q : ℝ) * c := hlt
  exact lt_irrefl _ this

/-- The seed selection in the form used by the incubation law: a pointwise seed density `c`
produces one seed whose good set carries at least the fraction `c` of the total mass. -/
theorem exists_measureReal_ge_of_pointwise [Nonempty Q] (A : Q → Set Ω)
    (hmeas : ∀ q, MeasurableSet (A q)) {c : ℝ}
    (hpt : ∀ x, (Fintype.card Q : ℝ) * c ≤ ∑ q, Set.indicator (A q) (1 : Ω → ℝ) x) :
    ∃ q, c * μ.real Set.univ ≤ μ.real (A q) := by
  refine exists_measureReal_ge (μ := μ) A ?_
  have hbase := sum_measureReal_ge_of_pointwise (μ := μ) A hmeas hpt
  calc (Fintype.card Q : ℝ) * (c * μ.real Set.univ)
      = (Fintype.card Q : ℝ) * c * μ.real Set.univ := by ring
    _ ≤ ∑ q, μ.real (A q) := hbase

end Selection

/-! ## The coefficient shell -/

section Shell

variable {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The discrete Cauchy--Schwarz bound behind the shell Lipschitz constant. -/
theorem sq_sum_abs_le_card_mul_sum_sq (c : ι → ℝ) :
    (∑ i, |c i|) ^ (2 : ℕ) ≤ (Fintype.card ι : ℝ) * ∑ i, c i ^ (2 : ℕ) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι) (fun _ => (1 : ℝ))
    fun i => |c i|
  have hone : ∑ i : ι, (1 : ℝ) * |c i| = ∑ i, |c i| := by
    simp
  have hcard : ∑ _i : ι, (1 : ℝ) ^ (2 : ℕ) = (Fintype.card ι : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    norm_num
  have habs : ∑ i, |c i| ^ (2 : ℕ) = ∑ i, c i ^ (2 : ℕ) :=
    Finset.sum_congr rfl fun i _ => sq_abs (c i)
  rw [hone, hcard, habs] at hcs
  exact hcs

/-- **`(22)`: the shell is Lipschitz with the square root of the generator count.**  A combination
of unit-norm generators has norm at most the `ℓ¹` norm of its coefficients. -/
theorem norm_sum_smul_le_sum_abs (c : ι → ℝ) (P : ι → E) (hP : ∀ i, ‖P i‖ ≤ 1) :
    ‖∑ i, c i • P i‖ ≤ ∑ i, |c i| := by
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) (hP i)

omit [NormedSpace ℝ E] in
/-- **`(21)`: half the edge coupling survives the tube.**  A centre whose edge block has norm at
least `b₀/s`, perturbed by at most `b₀/(2s)`, keeps norm at least `b₀/(2s)`. -/
theorem norm_ge_half_of_perturbation {V W : E} {b0 s ρ : ℝ} (hs : 0 < s)
    (hW : b0 / s ≤ ‖W‖) (hdiff : ‖V - W‖ ≤ ρ) (hρ : ρ ≤ b0 / (2 * s)) :
    b0 / (2 * s) ≤ ‖V‖ := by
  have htri : ‖W‖ - ‖V - W‖ ≤ ‖V‖ := by
    have h := norm_sub_norm_le W (W - V)
    have hWV : W - (W - V) = V := by abel
    rw [hWV] at h
    have hsym : ‖W - V‖ = ‖V - W‖ := norm_sub_rev W V
    rw [hsym] at h
    exact h
  have hsplit : b0 / s - b0 / (2 * s) = b0 / (2 * s) := by
    field_simp
    ring
  linarith [hW, hdiff, hρ, htri, hsplit.le, hsplit.ge]

end Shell

end

end GaloisForLFunctions.HTGeometry
