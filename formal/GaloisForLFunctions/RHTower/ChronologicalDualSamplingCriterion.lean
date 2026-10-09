import GaloisForLFunctions.RHTower.ChronologicalRiemannEquivalence
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# The dual sampling form of the chronological criterion

In the real Hilbert space `L²(0,∞)` let `E = e^{-t}` and `β_k(t) = β(kt)`,
`β(t) = 1/t − 1/(e^t − 1)`. The closed convex hull of all finite sums `Σ_{k ≤ N} a_k β_k` with
`|a_k| ≤ 1` contains `−E` exactly when every test vector `g` obeys the sampling inequality

  `|⟨g, E⟩| ≤ sup_N Σ_{k ≤ N} |⟨g, β_k⟩|`.

With the unit-row criterion (`riemannHypothesis_iff_chronological_unit_rows`) this gives
(`riemannHypothesis_iff_chronological_sampling`): RH holds iff
`|⟨g, e^{-t}⟩| ≤ B` whenever all partial sums `Σ_{k ≤ N} |⟨g, β(k·)⟩|` are at most `B`.

The inequality is the triangle inequality applied to Möbius inversion
`⟨g, e^{-t}⟩ = −Σ μ(k)⟨g, β(k·)⟩`, so RH is the validity of that inversion for every
`g ∈ L²(0,∞)` whose sampled values are absolutely summable.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
namespace RHTower
open GaloisForLFunctions.HTGeometry.ChronologicalTensor

/-- The real Hilbert space `L²(0,∞)`. -/
abbrev ChronologicalL2 := Lp ℝ 2 chronologicalPositiveVolume

/-- `e^{-t}` as a vector of `L²(0,∞)`. -/
def chronologicalExpL2 : ChronologicalL2 := chronologicalExponential_memLp.toLp _

/-- The integer dilate `β(kt)` as a vector of `L²(0,∞)` (zero for `k = 0`). -/
def chronologicalBoseL2 (k : ℕ) : ChronologicalL2 :=
  if hk : 0 < k then
    (chronological_memLp_dilate chronologicalBose_memLp chronologicalBose_continuousOn
      (by exact_mod_cast hk : (0:ℝ) < k)).toLp _
  else 0

theorem chronologicalL2_coeFn_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ChronologicalL2) :
    ((∑ i ∈ s, f i : ChronologicalL2) : ℝ → ℝ) =ᵐ[chronologicalPositiveVolume]
      fun x => ∑ i ∈ s, (f i : ℝ → ℝ) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero ℝ 2 chronologicalPositiveVolume] with x hx
    simpa using hx
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (f i) (∑ j ∈ s, f j), ih] with x hx hx'
    rw [hx, Pi.add_apply, hx', Finset.sum_insert hi]

/-- A finite heat residual is the vector `E + Σ_{k ≤ N} a_k β_k`. -/
theorem chronologicalHeatError_toLp (a : ℕ → ℝ) (N : ℕ) :
    (chronologicalHeatError_memLp a N).toLp _ =
      chronologicalExpL2 + ∑ k ∈ Finset.Ioc 0 N, a k • chronologicalBoseL2 k := by
  apply Lp.ext
  have hsum := chronologicalL2_coeFn_finset_sum (Finset.Ioc 0 N)
    (fun k => a k • chronologicalBoseL2 k)
  have hterms : ∀ k ∈ Finset.Ioc 0 N, ((a k • chronologicalBoseL2 k : ChronologicalL2) : ℝ → ℝ)
      =ᵐ[chronologicalPositiveVolume] fun t => a k * fusionBoseDefect ((k:ℝ) * t) := by
    intro k hk
    have hk0 : 0 < k := (Finset.mem_Ioc.mp hk).1
    filter_upwards [Lp.coeFn_smul (a k) (chronologicalBoseL2 k),
      (chronological_memLp_dilate chronologicalBose_memLp chronologicalBose_continuousOn
        (by exact_mod_cast hk0 : (0:ℝ) < k)).coeFn_toLp] with t ht ht'
    rw [ht, Pi.smul_apply, smul_eq_mul]
    unfold chronologicalBoseL2
    rw [dif_pos hk0, ht']
  have hall : ∀ᵐ t ∂chronologicalPositiveVolume, ∀ k ∈ Finset.Ioc 0 N,
      ((a k • chronologicalBoseL2 k : ChronologicalL2) : ℝ → ℝ) t =
        a k * fusionBoseDefect ((k:ℝ) * t) :=
    (ae_ball_iff (Finset.countable_toSet _)).mpr fun k hk => hterms k hk
  filter_upwards [(chronologicalHeatError_memLp a N).coeFn_toLp,
    Lp.coeFn_add chronologicalExpL2 (∑ k ∈ Finset.Ioc 0 N, a k • chronologicalBoseL2 k),
    chronologicalExponential_memLp.coeFn_toLp, hsum, hall] with t h1 h2 h3 h4 h5
  rw [h1, h2, Pi.add_apply, h4]
  unfold chronologicalExpL2
  rw [h3]
  unfold chronologicalHeatError
  congr 1
  exact Finset.sum_congr rfl fun k hk => (h5 k hk).symm

/-- The Hilbert norm of the residual vector is the chronological `L²` norm. -/
theorem norm_chronologicalHeatError_toLp (a : ℕ → ℝ) (N : ℕ) :
    ‖chronologicalExpL2 + ∑ k ∈ Finset.Ioc 0 N, a k • chronologicalBoseL2 k‖ =
      chronologicalL2Norm (chronologicalHeatError a N) := by
  rw [← chronologicalHeatError_toLp, Lp.norm_toLp, chronologicalL2Norm,
    toReal_eLpNorm (chronologicalHeatError_memLp a N).1]

/-- Finite sums `Σ_{k ≤ N} a_k β_k` with unit-bounded coefficients. -/
def chronologicalUnitRowSet : Set ChronologicalL2 :=
  {h | ∃ N : ℕ, ∃ a : ℕ → ℝ, (∀ k ∈ Finset.Ioc 0 N, |a k| ≤ 1) ∧
    h = ∑ k ∈ Finset.Ioc 0 N, a k • chronologicalBoseL2 k}

private theorem sum_Ioc_extend (a : ℕ → ℝ) {N M : ℕ} (hNM : N ≤ M) :
    (∑ k ∈ Finset.Ioc 0 N, a k • chronologicalBoseL2 k) =
      ∑ k ∈ Finset.Ioc 0 M, (if k ≤ N then a k else 0) • chronologicalBoseL2 k := by
  have hsub : Finset.Ioc 0 N ⊆ Finset.Ioc 0 M := Finset.Ioc_subset_Ioc_right hNM
  rw [← Finset.sum_subset hsub (fun k hkM hkN => ?_)]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [if_pos (Finset.mem_Ioc.mp hk).2]
  · have : ¬ k ≤ N := fun h => hkN (Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hkM).1, h⟩)
    rw [if_neg this, zero_smul]

theorem convex_chronologicalUnitRowSet : Convex ℝ chronologicalUnitRowSet := by
  rintro x ⟨N₁, a, ha, rfl⟩ y ⟨N₂, b, hb, rfl⟩ θ₁ θ₂ hθ₁ hθ₂ hθ
  refine ⟨max N₁ N₂, fun k => θ₁ * (if k ≤ N₁ then a k else 0) +
    θ₂ * (if k ≤ N₂ then b k else 0), ?_, ?_⟩
  · intro k hk
    have hk0 : 0 < k := (Finset.mem_Ioc.mp hk).1
    have h1 : |(if k ≤ N₁ then a k else 0)| ≤ 1 := by
      split_ifs with h
      · exact ha k (Finset.mem_Ioc.mpr ⟨hk0, h⟩)
      · simp
    have h2 : |(if k ≤ N₂ then b k else 0)| ≤ 1 := by
      split_ifs with h
      · exact hb k (Finset.mem_Ioc.mpr ⟨hk0, h⟩)
      · simp
    calc |θ₁ * (if k ≤ N₁ then a k else 0) + θ₂ * (if k ≤ N₂ then b k else 0)|
        ≤ θ₁ * |(if k ≤ N₁ then a k else 0)| + θ₂ * |(if k ≤ N₂ then b k else 0)| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg hθ₁, abs_of_nonneg hθ₂]
      _ ≤ θ₁ * 1 + θ₂ * 1 := by gcongr
      _ = 1 := by rw [mul_one, mul_one, hθ]
  · rw [sum_Ioc_extend a (le_max_left N₁ N₂), sum_Ioc_extend b (le_max_right N₁ N₂),
      Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [smul_smul, smul_smul, ← add_smul]

/-- **Dual sampling form of the chronological criterion.** RH holds iff every `g ∈ L²(0,∞)`
satisfies `|⟨g, e^{-t}⟩| ≤ B` whenever all partial sums `Σ_{k ≤ N} |⟨g, β(k·)⟩|` are at most
`B`. -/
theorem riemannHypothesis_iff_chronological_sampling :
    RiemannHypothesis ↔ ∀ (g : ChronologicalL2) (B : ℝ),
      (∀ N : ℕ, ∑ k ∈ Finset.Ioc 0 N, |⟪g, chronologicalBoseL2 k⟫| ≤ B) →
        |⟪g, chronologicalExpL2⟫| ≤ B := by
  rw [riemannHypothesis_iff_chronological_unit_rows]
  constructor
  · intro hrows g B hB
    have hg0 : 0 ≤ ‖g‖ := norm_nonneg g
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨N, a, ha, hsmall⟩ := hrows (ε / (‖g‖ + 1)) (by positivity)
    rw [← norm_chronologicalHeatError_toLp] at hsmall
    set R := chronologicalExpL2 + ∑ k ∈ Finset.Ioc 0 N, a k • chronologicalBoseL2 k
    have hE : chronologicalExpL2 = R - ∑ k ∈ Finset.Ioc 0 N, a k • chronologicalBoseL2 k := by
      simp [R]
    have hinner : ⟪g, chronologicalExpL2⟫ = ⟪g, R⟫ -
        ∑ k ∈ Finset.Ioc 0 N, a k * ⟪g, chronologicalBoseL2 k⟫ := by
      rw [hE, inner_sub_right, inner_sum]
      simp [inner_smul_right]
    have hR : |⟪g, R⟫| ≤ ‖g‖ * (ε / (‖g‖ + 1)) :=
      (abs_real_inner_le_norm g R).trans (mul_le_mul_of_nonneg_left hsmall.le hg0)
    have hsum : |∑ k ∈ Finset.Ioc 0 N, a k * ⟪g, chronologicalBoseL2 k⟫| ≤ B := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun k hk => ?_).trans (hB N))
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (ha k hk)
    have hfrac : ‖g‖ * (ε / (‖g‖ + 1)) < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    rw [hinner]
    calc |⟪g, R⟫ - ∑ k ∈ Finset.Ioc 0 N, a k * ⟪g, chronologicalBoseL2 k⟫|
        ≤ |⟪g, R⟫| + |∑ k ∈ Finset.Ioc 0 N, a k * ⟪g, chronologicalBoseL2 k⟫| := abs_sub _ _
      _ < B + ε := by linarith
  · intro hsamp ε hε
    have hmem : -chronologicalExpL2 ∈ closure chronologicalUnitRowSet := by
      by_contra hnot
      obtain ⟨φ, u, hφ, hu⟩ := geometric_hahn_banach_closed_point
        (convex_chronologicalUnitRowSet.closure) isClosed_closure hnot
      set g := (InnerProductSpace.toDual ℝ ChronologicalL2).symm φ
      have hgφ : ∀ x, ⟪g, x⟫ = φ x := fun x => by
        simp [g, InnerProductSpace.toDual_symm_apply]
      have hB : ∀ N : ℕ, ∑ k ∈ Finset.Ioc 0 N, |⟪g, chronologicalBoseL2 k⟫| ≤ u := by
        intro N
        set s : ℕ → ℝ := fun k => if 0 ≤ ⟪g, chronologicalBoseL2 k⟫ then 1 else -1
        have hmemN : (∑ k ∈ Finset.Ioc 0 N, s k • chronologicalBoseL2 k) ∈
            closure chronologicalUnitRowSet :=
          subset_closure ⟨N, s, fun k _ => by simp only [s]; split_ifs <;> norm_num, rfl⟩
        have hlt := hφ _ hmemN
        rw [← hgφ, inner_sum] at hlt
        refine le_of_lt (lt_of_eq_of_lt (Finset.sum_congr rfl fun k _ => ?_) hlt)
        rw [inner_smul_right]
        simp only [s]
        split_ifs with h
        · rw [one_mul, abs_of_nonneg h]
        · rw [abs_of_neg (not_le.mp h)]; ring
      have hle := hsamp g u hB
      have hneg : u < -⟪g, chronologicalExpL2⟫ := by
        rw [hgφ, ← map_neg]; exact hu
      have := neg_le_abs ⟪g, chronologicalExpL2⟫
      linarith
    obtain ⟨h, hhK, hdist⟩ := Metric.mem_closure_iff.mp hmem ε hε
    obtain ⟨N, a, ha, rfl⟩ := hhK
    refine ⟨N, a, ha, ?_⟩
    rw [← norm_chronologicalHeatError_toLp]
    rw [dist_eq_norm] at hdist
    have heq : -chronologicalExpL2 - ∑ k ∈ Finset.Ioc 0 N, a k • chronologicalBoseL2 k =
        -(chronologicalExpL2 + ∑ k ∈ Finset.Ioc 0 N, a k • chronologicalBoseL2 k) := by abel
    rwa [heq, norm_neg] at hdist

end RHTower
