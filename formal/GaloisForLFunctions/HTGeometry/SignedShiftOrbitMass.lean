import GaloisForLFunctions.HTGeometry.ShiftOrbitMassObstruction

/-!
# The shift-orbit mass obstruction with signed multiplicities

`not_shiftDifference_negSumInvSq_orbit` counts poles: every inverse square enters with weight one.
The obstruction needed to separate *Gamma monomials* has integer weights of both signs, because the
exponent vector of a ratio of two monomials is a difference.

Nothing in the argument depends on the weights being positive; only the total mass on the orbit
matters.  This file restates the Laurent-mass computation and the obstruction with arbitrary complex
weights, reusing the machinery of `ShiftOrbitMassObstruction` verbatim.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

/-- **The order-two mass of a weighted sum of inverse squares.** -/
theorem laurentCoeff_weightedSumInvSq {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (c p : ι → ℂ) (q : ℂ) :
    laurentCoeff (fun z => ∑ i ∈ s, c i * ((z - p i) ^ (2 : ℕ))⁻¹) q (-2)
      = ∑ i ∈ s.filter (fun i => p i = q), c i := by
  classical
  rw [laurentCoeff_sum s (fun i z => ((z - p i) ^ (2 : ℕ))⁻¹) c q (-2)
    (fun i _ => meromorphicAt_invSq (p i) q)]
  have hterm : ∀ i ∈ s, c i * laurentCoeff (fun z => ((z - p i) ^ (2 : ℕ))⁻¹) q (-2)
      = if p i = q then c i else 0 := by
    intro i _
    rcases eq_or_ne (p i) q with hpi | hpi
    · subst hpi
      rw [laurentCoeff_invSq_self, if_pos rfl, mul_one]
    · rw [laurentCoeff_invSq_of_ne (Ne.symm hpi), if_neg hpi, mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite, Finset.sum_const_zero, add_zero]

/-- **The signed shift-orbit mass obstruction.**  If the weights sitting on one `H`-orbit have
nonzero total, the weighted sum of inverse squares is not the shift difference of any meromorphic
function with finitely many poles. -/
theorem not_shiftDifference_weightedSumInvSq_orbit {H a : ℂ} (hH : H ≠ 0) {ι : Type*}
    [DecidableEq ι] (s : Finset ι) (c p : ι → ℂ) (s₀ : Finset ι) (hsub : s₀ ⊆ s) (ν : ι → ℤ)
    (hp : ∀ i ∈ s₀, p i = a + (ν i : ℂ) * H)
    (hoff : ∀ i ∈ s, i ∉ s₀ → ∀ n : ℤ, p i ≠ a + (n : ℂ) * H)
    (hmass : ∑ i ∈ s₀, c i ≠ 0)
    {y : ℂ → ℂ} (hy : MeromorphicOn y Set.univ)
    (hpoles : {z : ℂ | ¬ AnalyticAt ℂ y z}.Finite) :
    ¬ ((fun z => y (z + H) - y z)
        =ᶠ[Filter.cofinite] fun z => ∑ i ∈ s, c i * ((z - p i) ^ (2 : ℕ))⁻¹) := by
  classical
  intro heq
  have hinj : Function.Injective fun n : ℤ => a + (n : ℂ) * H := by
    intro m n hmn
    have h1 : (m : ℂ) * H = (n : ℂ) * H := by linear_combination hmn
    have hcast : (m : ℂ) = (n : ℂ) := mul_right_cancel₀ hH h1
    exact_mod_cast hcast
  set d : ℤ → ℂ := fun n => laurentCoeff y (a + (n : ℂ) * H) (-2) with hd
  have hsupp : {n : ℤ | d n ≠ 0}.Finite := by
    refine Set.Finite.subset (Set.Finite.preimage (f := fun n : ℤ => a + (n : ℂ) * H)
      (hinj.injOn) hpoles) ?_
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    intro hana
    exact hn (laurentCoeff_eq_zero_of_analyticAt hana (by norm_num))
  obtain ⟨N₁, hN₁⟩ := exists_symmetric_support_bound hsupp
  obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ, ∀ i ∈ s₀, -(N₂ : ℤ) ≤ ν i ∧ ν i < (N₂ : ℤ) := by
    refine ⟨(s₀.image fun i => (ν i).natAbs).sup id + 1, fun i hi => ?_⟩
    have hle : (ν i).natAbs ≤ (s₀.image fun i => (ν i).natAbs).sup id :=
      Finset.le_sup (f := id) (Finset.mem_image_of_mem _ hi)
    constructor <;> [skip; skip] <;> · push_cast; omega
  set N : ℕ := max N₁ N₂ with hN
  have hout : ∀ n : ℤ, (n ≤ -(N : ℤ) ∨ (N : ℤ) ≤ n) → d n = 0 := by
    intro n hn
    by_contra hne
    obtain ⟨h1, h2⟩ := hN₁ n hne
    have : (N₁ : ℤ) ≤ (N : ℤ) := by exact_mod_cast le_max_left N₁ N₂
    omega
  have hzero := sum_Ico_laurentCoeff_shiftDiff_eq_zero (y := y) hy (H := H) (a := a) (ℓ := -2)
    (N := N) hout
  have hterm : ∀ n : ℤ,
      laurentCoeff (fun z => y (z + H) - y z) (a + (n : ℂ) * H) (-2)
        = ∑ i ∈ s.filter (fun i => p i = a + (n : ℂ) * H), c i := by
    intro n
    have hmero : MeromorphicAt (fun z => y (z + H) - y z) (a + (n : ℂ) * H) :=
      (meromorphicAt_comp_add.mpr (hy _ (Set.mem_univ _))).sub (hy _ (Set.mem_univ _))
    rw [laurentCoeff_congr hmero (heq.filter_mono (nhdsNE_le_cofinite _)) (-2),
      laurentCoeff_weightedSumInvSq]
  rw [Finset.sum_congr rfl fun n _ => hterm n] at hzero
  have hmaps : Set.MapsTo ν ↑s₀ ↑(Finset.Ico (-(N : ℤ)) (N : ℤ)) := by
    intro i hi
    have hi' : i ∈ s₀ := hi
    obtain ⟨h1, h2⟩ := hN₂ i hi'
    have : (N₂ : ℤ) ≤ (N : ℤ) := by exact_mod_cast le_max_right N₁ N₂
    simp only [Finset.coe_Ico, Set.mem_Ico]
    omega
  have hfiber : ∀ n ∈ Finset.Ico (-(N : ℤ)) (N : ℤ),
      (s.filter fun i => p i = a + (n : ℂ) * H) = s₀.filter fun i => ν i = n := by
    intro n _
    ext i
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨his, hpi⟩
      have hi₀ : i ∈ s₀ := by
        by_contra hcon
        exact hoff i his hcon n hpi
      refine ⟨hi₀, hinj ?_⟩
      show a + ((ν i : ℤ) : ℂ) * H = a + (n : ℂ) * H
      rw [← hp i hi₀, hpi]
    · rintro ⟨hi₀, hν⟩
      exact ⟨hsub hi₀, by rw [hp i hi₀, hν]⟩
  have hsum : ∑ n ∈ Finset.Ico (-(N : ℤ)) (N : ℤ),
      (∑ i ∈ s.filter (fun i => p i = a + (n : ℂ) * H), c i) = ∑ i ∈ s₀, c i := by
    rw [Finset.sum_congr rfl fun n hn => by rw [hfiber n hn]]
    exact Finset.sum_fiberwise_of_maps_to hmaps c
  rw [hsum] at hzero
  exact hmass hzero

end

end GaloisForLFunctions.HTGeometry
