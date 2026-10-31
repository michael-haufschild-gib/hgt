import GaloisForLFunctions.AdelicKreinGeometry.Haar.CyclicGramLimit
import GaloisForLFunctions.AdelicKreinGeometry.Haar.PolynomialCorrection
import GaloisForLFunctions.AdelicKreinGeometry.Haar.ContinuousDilationsNeedInfiniteIndex
import GaloisForLFunctions.HTGeometry.InertiaScalingSwap

/-!
# Punctured dilation limits of Haar carriers

The common limit through nonidentity positive rational dilations is real for a
Hermitian carrier. A positive limit makes cyclic fixed-projection Grams approach
a positive multiple of `J − I`, forcing infinite negative index. Positive Haar
carriers themselves have punctured limit zero.
-/

open Complex Finset Filter Topology Matrix Module
open scoped ComplexConjugate
open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.BiarithmeticGeometry
open GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace GaloisForLFunctions.AdelicKreinGeometry

/-- The real-topology limit through positive rational dilations other than identity. -/
def HasPuncturedDilationLimit (k : AffineGroupQ → ℂ) (L : ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ u : ℚˣ,
    0 < (u : ℚ) → u ≠ 1 → |((u : ℚ) : ℝ) - 1| < δ → ‖k (dilation u) - L‖ < ε

/-- The punctured limit controls every nonidentity positive rational sequence approaching one. -/
theorem HasPuncturedDilationLimit.tendsto {k : AffineGroupQ → ℂ} {L : ℂ}
    (hL : HasPuncturedDilationLimit k L) (u : ℕ → ℚˣ)
    (hpos : ∀ n, 0 < (u n : ℚ)) (hne : ∀ n, u n ≠ 1)
    (hu : Tendsto (fun n => ((u n : ℚ) : ℝ)) atTop (𝓝 1)) :
    Tendsto (fun n => k (dilation (u n))) atTop (𝓝 L) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hL ε hε
  filter_upwards [Metric.tendsto_nhds.mp hu δ hδ] with n hn
  rw [Real.dist_eq] at hn
  simpa only [dist_eq_norm] using hbound (u n) (hpos n) (hne n) hn

private theorem nearIdentityUnit_one_ne (n : ℕ) : nearIdentityUnit n 1 ≠ 1 := by
  have hzero : nearIdentityUnit n 0 = 1 := by
    apply Units.ext
    simp only [nearIdentityUnit, Units.val_mk0, Nat.cast_zero, zero_div, add_zero, Units.val_one]
  intro h
  have he := nearIdentityUnit_injective n (h.trans hzero.symm)
  exact Nat.one_ne_zero he

/-- Nonidentity rational units approaching one make the punctured limit unique. -/
theorem HasPuncturedDilationLimit.unique {k : AffineGroupQ → ℂ} {L M : ℂ}
    (hL : HasPuncturedDilationLimit k L) (hM : HasPuncturedDilationLimit k M) : L = M :=
  tendsto_nhds_unique
    (hL.tendsto (fun n => nearIdentityUnit n 1) (fun n => nearIdentityUnit_pos n 1)
      nearIdentityUnit_one_ne (tendsto_nearIdentityUnit 1))
    (hM.tendsto (fun n => nearIdentityUnit n 1) (fun n => nearIdentityUnit_pos n 1)
      nearIdentityUnit_one_ne (tendsto_nearIdentityUnit 1))

/-- Hermitian symmetry and inversion force a common punctured dilation limit to be real. -/
theorem HasPuncturedDilationLimit.ofReal_re {k : AffineGroupQ → ℂ} {L : ℂ}
    (hL : HasPuncturedDilationLimit k L) (hk : IsHermKernel k) : (L.re : ℂ) = L := by
  let u : ℕ → ℚˣ := fun n => nearIdentityUnit n 1
  have hu : Tendsto (fun n => ((u n : ℚ) : ℝ)) atTop (𝓝 1) := tendsto_nearIdentityUnit 1
  have hseq := hL.tendsto u (fun n => nearIdentityUnit_pos n 1) nearIdentityUnit_one_ne hu
  have hinv : Tendsto (fun n => ((((u n)⁻¹ : ℚˣ) : ℚ) : ℝ)) atTop (𝓝 1) := by
    simpa only [Units.val_inv_eq_inv_val, Rat.cast_inv, inv_one] using hu.inv₀ one_ne_zero
  have hne_inv (n : ℕ) : (u n)⁻¹ ≠ 1 := by
    intro he
    apply nearIdentityUnit_one_ne n
    simpa only [inv_inv, inv_one] using congrArg (fun v : ℚˣ => v⁻¹) he
  have hseqinv := hL.tendsto (fun n => (u n)⁻¹)
    (fun n => by simpa only [Units.val_inv_eq_inv_val] using
      inv_pos.mpr (nearIdentityUnit_pos n 1)) hne_inv hinv
  have hstar : Tendsto (fun n => k (dilation ((u n)⁻¹))) atTop (𝓝 (conj L)) := by
    have he (n : ℕ) : k (dilation ((u n)⁻¹)) = conj (k (dilation (u n))) := by
      rw [map_inv]
      exact hk (dilation (u n))
    simpa only [he, Complex.star_def] using hseq.star
  exact Complex.conj_eq_iff_re.mp (tendsto_nhds_unique hstar hseqinv)

/-- A zero-axis change leaves the punctured dilation limit unchanged. -/
theorem HasPuncturedDilationLimit.sub_zero_axis {k q : AffineGroupQ → ℂ} {L : ℂ}
    (hL : HasPuncturedDilationLimit k L) (hq : ∀ u : ℚˣ, q (dilation u) = 0) :
    HasPuncturedDilationLimit (fun g => k g - q g) L := by
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hL ε hε
  refine ⟨δ, hδ, ?_⟩
  intro u hu hne hclose
  simpa only [hq, sub_zero] using hbound u hu hne hclose

/-- Positive Haar carriers have punctured limit zero, with radius `ε²` for error `ε`. -/
theorem hasPuncturedDilationLimit_zero_of_positive {p : AffineGroupQ → ℂ}
    (hp : IsPosDefKernel p) (hs : HasIntegerSuccessor p) : HasPuncturedDilationLimit p 0 := by
  intro ε hε
  refine ⟨ε ^ 2, sq_pos_of_pos hε, ?_⟩
  intro u _ hne hclose
  have hb := normSq_dilation_le_abs_sub_one hp hs u hne
  rw [Complex.normSq_eq_norm_sq] at hb
  rw [sub_zero]
  nlinarith only [hb, hclose, hε, norm_nonneg (p (dilation u))]

/-- A real punctured limit determines the full limiting cyclic fixed-projection Gram. -/
theorem tendsto_nearIdentity_projected_gram_of_punctured_limit {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r) (hs : HasIntegerSuccessor k)
    (hp : ∀ g, k (g * translation 1) = k g) {a : ℝ}
    (hL : HasPuncturedDilationLimit k (a : ℂ)) (n : ℕ) (i j : Fin n) :
    Tendsto (fun N => kernelColumnGram k (fun b : Fin n =>
      translationFixedProjection k hp (nearIdentityStep N)
        (kernelColumnPoint k (dilation (nearIdentityUnit N b)))) i j)
      atTop (𝓝 (((a : ℂ) • (Matrix.of (fun _ _ : Fin n => (1 : ℂ)) - 1)) i j)) := by
  by_cases hij : i = j
  · subst j
    simpa only [kernelColumnGram, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply,
      Matrix.of_apply, Matrix.one_apply_eq, sub_self, mul_zero] using
      tendsto_nearIdentity_projection_pairing hk hs hp i
  · have hne : i.val ≠ j.val := fun he => hij (Fin.ext he)
    have hz := tendsto_nearIdentity_moving_pairing hk hi hs hp hne
    have hpos (N : ℕ) :
        (0 : ℚ) < (((nearIdentityUnit N i)⁻¹ * nearIdentityUnit N j : ℚˣ) : ℚ) := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val]
      exact mul_pos (inv_pos.mpr (nearIdentityUnit_pos N i)) (nearIdentityUnit_pos N j)
    have hratio (N : ℕ) : (nearIdentityUnit N i)⁻¹ * nearIdentityUnit N j ≠ 1 := by
      intro he
      have he' : nearIdentityUnit N j = nearIdentityUnit N i := by
        have hm := congrArg (fun v : ℚˣ => nearIdentityUnit N i * v) he
        simpa only [mul_inv_cancel_left, mul_one] using hm
      exact hne ((nearIdentityUnit_injective N he').symm)
    have hfull := hL.tendsto (fun N => (nearIdentityUnit N i)⁻¹ * nearIdentityUnit N j)
      hpos hratio (tendsto_nearIdentityRatio i j)
    have hentry (N : ℕ) : kernelColumnGram k (fun b : Fin n =>
        translationFixedProjection k hp (nearIdentityStep N)
          (kernelColumnPoint k (dilation (nearIdentityUnit N b)))) i j =
        k (dilation ((nearIdentityUnit N i)⁻¹ * nearIdentityUnit N j)) -
          kernelColumnPairing k
            (movingDilationColumn k hp (nearIdentityStep N) (nearIdentityUnit N i))
            (movingDilationColumn k hp (nearIdentityStep N) (nearIdentityUnit N j)) := by
      have hspl := kernelColumnPairing_projection_decomposition hk (translation (nearIdentityStep N))
        (kernel_translation_locally_periodic hp (nearIdentityStep N))
        (kernelColumnPoint k (dilation (nearIdentityUnit N i)))
        (kernelColumnPoint k (dilation (nearIdentityUnit N j)))
      have hpair : kernelColumnPairing k
          (kernelColumnPoint k (dilation (nearIdentityUnit N i)))
          (kernelColumnPoint k (dilation (nearIdentityUnit N j))) =
          k (dilation ((nearIdentityUnit N i)⁻¹ * nearIdentityUnit N j)) := by
        rw [kernelColumnPairing_point_left hk]
        change k ((dilation (nearIdentityUnit N i))⁻¹ * dilation (nearIdentityUnit N j)) = _
        rw [← map_inv, ← map_mul]
      rw [hpair] at hspl
      simpa only [kernelColumnGram, translationFixedProjection, movingDilationColumn_eq_sub] using
        eq_sub_of_add_eq hspl.symm
    have hlim := (hfull.sub hz).congr' (Eventually.of_forall fun N => (hentry N).symm)
    simpa only [sub_zero, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, Matrix.of_apply,
      Matrix.one_apply_ne hij, mul_one] using hlim

/-- A positive punctured limit forces infinite index after integer periods are restored. -/
theorem negIndex_eq_top_of_integer_invariant_haar_positive_punctured_limit
    {k : AffineGroupQ → ℂ} (hk : IsHermKernel k) (hs : HasIntegerSuccessor k)
    (hp : ∀ g, k (g * translation 1) = k g) {a : ℝ} (ha : 0 < a)
    (hL : HasPuncturedDilationLimit k (a : ℂ)) : negIndex k = ⊤ := by
  have hno (r : ℕ) (hi : negIndex k ≤ r) : False := by
    let H : Matrix (Fin (r + 2)) (Fin (r + 2)) ℂ :=
      (a : ℂ) • (Matrix.of (fun _ _ => 1) - 1)
    have hH : H.IsHermitian := by
      ext i j
      change conj ((a : ℂ) * (1 - (if j = i then 1 else 0))) =
        (a : ℂ) * (1 - (if i = j then 1 else 0))
      by_cases hij : i = j
      · simp only [hij, ite_true, sub_self, mul_zero, map_zero]
      · simp only [hij, Ne.symm hij, ite_false, sub_zero, mul_one, Complex.conj_ofReal]
    have hc := tendsto_nearIdentity_projected_gram_of_punctured_limit hk hi hs hp hL (r + 2)
    obtain ⟨N, hN⟩ := (eventually_le_hermNegIndex hH hc).exists
    have hlow : r + 1 ≤ hermNegIndex H := by
      dsimp only [H]
      rw [negIndex_smul_pos ha]
      exact constant_sub_one_index_lower 1 (r + 1)
    have hu := hermNegIndex_kernelColumnGram_le hk hi (fun b : Fin (r + 2) =>
      translationFixedProjection k hp (nearIdentityStep N)
        (kernelColumnPoint k (dilation (nearIdentityUnit N b))))
    have he : r + 1 ≤ r := hlow.trans (hN.trans hu)
    omega
  refine ENat.eq_top_iff_forall_ge.mpr fun n => ?_
  by_contra hn
  exact hno n (le_of_lt (lt_of_not_ge hn))

/-- Every positive punctured limit is incompatible with finite index of a Haar carrier. -/
theorem negIndex_eq_top_of_haar_positive_punctured_limit {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) (hs : HasIntegerSuccessor k) {a : ℝ} (ha : 0 < a)
    (hL : HasPuncturedDilationLimit k (a : ℂ)) : negIndex k = ⊤ := by
  have hno (r : ℕ) (hi : negIndex k ≤ r) : False := by
    obtain ⟨q, _, _, _, hqt, hqd, hrem, hindex, hperiod, _⟩ :=
      exists_zero_axis_polynomial_correction hk hi (hasIntegerSuccessor_translation_periodic hs)
    have hsrem : HasIntegerSuccessor (fun g => k g - q g) := by
      intro b
      change k (translation b) - q (translation b) = _
      rw [hqt, sub_zero]
      exact hs b
    have htop := negIndex_eq_top_of_integer_invariant_haar_positive_punctured_limit
      hrem hsrem hperiod ha (hL.sub_zero_axis hqd)
    rw [htop] at hindex
    simp at hindex
  refine ENat.eq_top_iff_forall_ge.mpr fun n => ?_
  by_contra hn
  exact hno n (le_of_lt (lt_of_not_ge hn))

/-- Existing punctured dilation limits of finite-index Haar carriers are real and nonpositive. -/
theorem haar_punctured_limit_real_nonpositive {k : AffineGroupQ → ℂ} {L : ℂ}
    (hk : IsHermKernel k) (hs : HasIntegerSuccessor k) (hi : negIndex k < ⊤)
    (hL : HasPuncturedDilationLimit k L) : (L.re : ℂ) = L ∧ L.re ≤ 0 := by
  have he := hL.ofReal_re hk
  refine ⟨he, ?_⟩
  by_contra hpos
  have hlim : HasPuncturedDilationLimit k (L.re : ℂ) := by rwa [he]
  have htop := negIndex_eq_top_of_haar_positive_punctured_limit hk hs (lt_of_not_ge hpos) hlim
  exact (ne_of_lt hi) htop

#print axioms HasPuncturedDilationLimit.ofReal_re
#print axioms hasPuncturedDilationLimit_zero_of_positive
#print axioms negIndex_eq_top_of_haar_positive_punctured_limit
#print axioms haar_punctured_limit_real_nonpositive
end GaloisForLFunctions.AdelicKreinGeometry
