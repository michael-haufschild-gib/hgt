import GaloisForLFunctions.EffectiveArithmeticHodgeTheory.FiniteWeilPerturbationsHaveExplicitBounds

/-!
# Explicit finite horizon tests for the full Weil index

Negative eigenvectors give a finite compression with a definite margin.
The actual Euler–Maclaurin errors, polarized and compressed entry by entry,
retain its entire negative dimension whenever a stated finite inequality holds.
-/

noncomputable section
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
open MeasureTheory Matrix Finset Zeta23
open scoped ContDiff ComplexConjugate
namespace GaloisForLFunctions.EffectiveArithmeticHodgeTheory
open HTGeometry SpacingScaleHarmonicAnalysis
open ArithmeticCastelnuovoSeveri (weilGram cx)
open ArithmeticElectrostatics (atomicTest)

local notation "Λw" => (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ))

/-- Entrywise transport of an error budget through a rectangular compression. -/
def compressedEntryBudget {n r : ℕ} (S : Matrix (Fin n) (Fin r) ℂ)
    (B : Matrix (Fin n) (Fin n) ℝ) (i j : Fin r) : ℝ :=
  ∑ a, ∑ b, ‖S a i‖ * B a b * ‖S b j‖

private theorem norm_compression_le {n r : ℕ} (S : Matrix (Fin n) (Fin r) ℂ)
    (E : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin n) ℝ)
    (hE : ∀ a b, ‖E a b‖ ≤ B a b) (i j : Fin r) :
    ‖(Sᴴ * E * S) i j‖ ≤ compressedEntryBudget S B i j := by
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  apply (norm_sum_le _ _).trans
  unfold compressedEntryBudget
  apply sum_le_sum
  intro a _
  rw [Matrix.conjTranspose_apply, Matrix.mul_apply, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro b _
  rw [norm_mul, norm_mul, norm_star]
  have h := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (hE a b) (norm_nonneg (S b j))) (norm_nonneg (S a i))
  simpa only [mul_assoc] using h

/-- A finite compressed entry test retains every direction of a negative diagonal. -/
theorem le_index_of_compressed_entry_test {n r : ℕ}
    (A G : Matrix (Fin n) (Fin n) ℂ) (S : Matrix (Fin n) (Fin r) ℂ)
    (c : Fin r → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hc : ∀ i, c i ≤ -δ) (hdiag : Sᴴ * A * S = diagonal (fun i => (c i : ℂ)))
    (B : Matrix (Fin n) (Fin n) ℝ)
    (hE : ∀ a b, ‖G a b - A a b‖ ≤ B a b)
    (hsmall : ∀ i j, compressedEntryBudget S B i j ≤
      δ / (2 * ((r : ℝ) ^ 2 + 1))) :
    r ≤ hermNegIndex G := by
  let ε : ℝ := δ / (2 * ((r : ℝ) ^ 2 + 1))
  have hε : 0 ≤ ε := by dsimp only [ε]; positivity
  have hεr : ε * (r : ℝ) ^ 2 < δ := by
    dsimp only [ε]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith only [hδ, mul_nonneg hδ.le (sq_nonneg (r : ℝ))]
  have heq : Sᴴ * G * S - diagonal (fun i => (c i : ℂ)) = Sᴴ * (G - A) * S := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hdiag]
  have hentry (i j : Fin r) :
      ‖(Sᴴ * G * S - diagonal (fun i => (c i : ℂ))) i j‖ ≤ ε := by
    rw [heq]
    exact (norm_compression_le S (G - A) B hE i j).trans (hsmall i j)
  refine (Fintype.card_fin r).symm.le.trans
    (HeckeKreinToeplitz.card_le_hermNegIndex_of_forall_neg G S.mulVecLin ?_)
  intro x hx
  rw [Matrix.mulVecLin_apply, ← hermQuad_rect_conjugate]
  have hbound := (Complex.abs_re_le_norm _).trans
    (norm_quadForm_le_of_entries
      (Sᴴ * G * S - diagonal (fun i => (c i : ℂ))) hε hentry x)
  have hsub : hermQuad (Sᴴ * G * S) x -
      hermQuad (diagonal (fun i => (c i : ℂ))) x =
      (star x ⬝ᵥ (Sᴴ * G * S - diagonal (fun i => (c i : ℂ))) *ᵥ x).re := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]
    rfl
  have hbase := re_quadForm_diagonal_le_margin c hδ.le hc x
  have hx2 : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx) 2
  have hcost := mul_lt_mul_of_pos_right hεr hx2
  have hupper := (abs_le.mp hbound).2
  change hermQuad (diagonal (fun i => (c i : ℂ))) x ≤ _ at hbase
  linarith only [hsub, hbase, hcost, hupper]

/-- Every Hermitian matrix supplies its own complete negative compression and margin. -/
theorem exists_complete_negative_compression {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) :
    ∃ (r : ℕ) (S : Matrix (Fin n) (Fin r) ℂ) (c : Fin r → ℝ) (δ : ℝ),
      r = hermNegIndex A ∧ 0 < δ ∧ (∀ i, c i ≤ -δ) ∧
      Sᴴ * A * S = diagonal (fun i => (c i : ℂ)) := by
  classical
  let s : Finset (Fin n) := {i | hA.eigenvalues i < 0}
  let f : Fin s.card → Fin n := fun j => (s.equivFin.symm j : Fin n)
  have hf : Function.Injective f := fun j k h => s.equivFin.symm.injective (Subtype.ext h)
  let U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
  let S : Matrix (Fin n) (Fin s.card) ℂ := U.submatrix id f
  let c : Fin s.card → ℝ := fun j => hA.eigenvalues (f j)
  have hc : ∀ j, c j < 0 := fun j => (Finset.mem_filter.mp (s.equivFin.symm j).2).2
  have hdiag : Sᴴ * A * S = diagonal (fun j => (c j : ℂ)) := by
    have hcomp : Sᴴ * A * S = (Uᴴ * A * U).submatrix f f := by
      rw [submatrix_mul _ _ f id f Function.bijective_id,
        submatrix_mul _ _ f id id Function.bijective_id,
        submatrix_id_id, conjTranspose_submatrix]
    rw [hcomp, conjTranspose_mul_mul_eigenvectorUnitary hA, submatrix_diagonal _ _ hf]
    rfl
  have hr : s.card = hermNegIndex A := (negIndex_eq_card_neg_eigenvalues hA).symm
  rcases Nat.eq_zero_or_pos s.card with hz | hp
  · refine ⟨s.card, S, c, 1, hr, one_pos, ?_, hdiag⟩
    intro i
    have hi := i.isLt
    exact (by omega : False).elim
  · obtain ⟨i, _, hi⟩ := exists_min_image univ (fun j => -c j) ⟨⟨0, hp⟩, mem_univ _⟩
    refine ⟨s.card, S, c, -c i, hr, neg_pos.mpr (hc i), ?_, hdiag⟩
    intro j
    linarith only [hi j (mem_univ j)]


/-- Polarization budget for one entry of a real Weil family. -/
def weilGramEntryBudget {ι : Type*} (F : ι → ℝ → ℝ) (R e L k : ℝ)
    (i j : ι) : ℝ :=
  (weilPerturbationBudget (fun u => F i u + F j u) R (2 * e)
      (synthLevy R (2 * e) (2 * L) k) +
    weilPerturbationBudget (fun u => F i u - F j u) R (2 * e)
      (synthLevy R (2 * e) (2 * L) k)) / 4

/-- A common translation preserves the full Weil Gram matrix of real sources. -/
theorem weilGram_cx_common_translate {ι : Type*} (F : ι → ℝ → ℝ)
    (hF : ∀ i, ContDiff ℝ 2 (F i)) (hFc : ∀ i, HasCompactSupport (F i)) (t : ℝ) :
    weilGram Λw (fun i => cx (fun u => F i (u - t))) = weilGram Λw (fun i => cx (F i)) := by
  funext i j
  have htr (a : ι) : HasCompactSupport (fun u => F a (u - t)) :=
    (hFc a).comp_homeomorph (Homeomorph.subRight t)
  have htr2 (a : ι) : ContDiff ℝ 2 (fun u => F a (u - t)) :=
    (hF a).comp (contDiff_id.sub contDiff_const)
  change RHTower.weilFullFunctional Λw
    (EF.weilTest (cx (fun u => F i (u - t))) (cx (fun u => F j (u - t)))) =
    RHTower.weilFullFunctional Λw (EF.weilTest (cx (F i)) (cx (F j)))
  rw [weilPair_real_eq (htr2 i) (htr i) (htr2 j) (htr j),
    weilPair_real_eq (hF i) (hFc i) (hF j) (hFc j)]
  rw [weilQuad_comp_sub (fun u => F i u + F j u),
    weilQuad_comp_sub (fun u => F i u - F j u)]

/-- The entry budget of the actual Euler–Maclaurin synthesis at a finite horizon. -/
def emWeilEntryBudget {n : ℕ} (F : Fin n → ℝ → ℝ) (φ : ℝ → ℝ)
    (M : ℕ → ℝ) (R : ℝ) (m : ℕ) (k : ℝ) (N : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  weilGramEntryBudget F (R + 1)
    (emErr M (fun q => ∫ u, |iteratedDeriv q φ u|) m k N)
    (emLip M (fun q => ∫ u, |iteratedDeriv q φ u|) k N) k

/-- The full index of each finite real Weil family has an explicit finite-horizon
synthesis test. The errors are the proved Euler–Maclaurin errors of the actual profile. -/
theorem exists_emWeil_index_horizon_test {n : ℕ} (F : Fin n → ℝ → ℝ)
    {R : ℝ} (hR : 0 ≤ R) (hF : ∀ i, ContDiff ℝ ∞ (F i))
    (hFR : ∀ i, SupportedIn R (F i)) :
    ∃ (r : ℕ) (S : Matrix (Fin n) (Fin r) ℂ) (δ : ℝ),
      r = hermNegIndex (weilGram Λw (fun i => cx (F i))) ∧ 0 < δ ∧
      ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → VanishesOff φ → (∫ u, φ u) = 1 →
      ∀ (M : ℕ → ℝ), (∀ l, 0 ≤ M l) → (∀ i l u, |iteratedDeriv l (F i) u| ≤ M l) →
      ∀ (m N : ℕ) (k : ℝ), 2 ≤ N → 1 ≤ k →
      (∀ i j, compressedEntryBudget S (emWeilEntryBudget F φ M R m k N) i j ≤
        δ / (2 * ((r : ℝ) ^ 2 + 1))) →
      r ≤ hermNegIndex (atomicGram (dilate k φ) (N * blockSize R)) := by
  have hF2 (i : Fin n) := (hF i).of_le (natCast_le_infty 2)
  have hFc (i : Fin n) := hasCompactSupport_of_vanishes (hFR i)
  obtain ⟨r, S, c, δ, hr, hδ, hc, hdiag⟩ := exists_complete_negative_compression
    (weilGram Λw (fun i => cx (F i))) (weilGram_cx_isHermitian hF2 hFc)
  refine ⟨r, S, δ, hr, hδ, ?_⟩
  intro φ hφ hφ1 hφint M hM0 hM m N k hN hk hsmall
  have hk0 : 0 < k := lt_of_lt_of_le zero_lt_one hk
  choose x D hx hD hDR he hL using
    (fun i => exists_emSynthesis hφ hφ1 hφint (hF i) (hFR i) (hM i) hM0 hN hk m)
  have hGD (i : Fin n) : ContDiff ℝ 2 (fun u => F i u + D i u) := (hF2 i).add (hD i)
  have hGDc (i : Fin n) : HasCompactSupport (fun u => F i u + D i u) :=
    (hFc i).add (hasCompactSupport_of_vanishes (hDR i))
  have hGram : weilGram Λw (fun i => cx (atomicTest (N * blockSize R) (x i) (dilate k φ))) =
      weilGram Λw (fun i => cx (fun u => F i u + D i u)) := by
    simp_rw [hx]
    exact weilGram_cx_common_translate (fun i u => F i u + D i u) hGD hGDc _
  have hentry (i j : Fin n) :
      ‖weilGram Λw (fun i => cx (fun u => F i u + D i u)) i j -
        weilGram Λw (fun i => cx (F i)) i j‖ ≤ emWeilEntryBudget F φ M R m k N i j := by
    exact norm_weilGram_add_sub_le_explicit F D hF2 hFc
      (fun i => supportedIn_mono (hFR i) (by linarith only)) hD hDR
      (by linarith only [hR]) he hL hk i j
  have hindex := le_index_of_compressed_entry_test _ _ S c hδ hc hdiag _ hentry hsmall
  rw [← hGram] at hindex
  exact hindex.trans (hermNegIndex_le_atomicGram (hφ.of_le (natCast_le_infty 2)) hφ1 hk0 x)


/-- Smooth compact source data themselves supply every derivative bound used in the test. -/
theorem exists_emWeil_index_horizon_certificate {n : ℕ} (F : Fin n → ℝ → ℝ)
    {R : ℝ} (hR : 0 ≤ R) (hF : ∀ i, ContDiff ℝ ∞ (F i))
    (hFR : ∀ i, SupportedIn R (F i)) :
    ∃ (M : ℕ → ℝ) (r : ℕ) (S : Matrix (Fin n) (Fin r) ℂ) (δ : ℝ),
      (∀ l, 0 ≤ M l) ∧ (∀ i l u, |iteratedDeriv l (F i) u| ≤ M l) ∧
      r = hermNegIndex (weilGram Λw (fun i => cx (F i))) ∧ 0 < δ ∧
      ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → VanishesOff φ → (∫ u, φ u) = 1 →
      ∀ (m N : ℕ) (k : ℝ), 2 ≤ N → 1 ≤ k →
      (∀ i j, compressedEntryBudget S (emWeilEntryBudget F φ M R m k N) i j ≤
        δ / (2 * ((r : ℝ) ^ 2 + 1))) →
      r ≤ hermNegIndex (atomicGram (dilate k φ) (N * blockSize R)) := by
  classical
  choose Mi hMi0 hMi using
    (fun i => exists_iteratedDeriv_bounds (hF i) (hasCompactSupport_of_vanishes (hFR i)))
  let M : ℕ → ℝ := fun l => ∑ i, Mi i l
  have hM0 (l : ℕ) : 0 ≤ M l := sum_nonneg fun i _ => hMi0 i l
  have hM (i : Fin n) (l : ℕ) (u : ℝ) : |iteratedDeriv l (F i) u| ≤ M l :=
    (hMi i l u).trans (single_le_sum (fun j _ => hMi0 j l) (mem_univ i))
  obtain ⟨r, S, δ, hr, hδ, htest⟩ := exists_emWeil_index_horizon_test F hR hF hFR
  exact ⟨M, r, S, δ, hM0, hM, hr, hδ,
    fun φ hφ hφ1 hφint => htest φ hφ hφ1 hφint M hM0 hM⟩

end GaloisForLFunctions.EffectiveArithmeticHodgeTheory

#print axioms GaloisForLFunctions.EffectiveArithmeticHodgeTheory.le_index_of_compressed_entry_test
#print axioms GaloisForLFunctions.EffectiveArithmeticHodgeTheory.exists_complete_negative_compression

#print axioms GaloisForLFunctions.EffectiveArithmeticHodgeTheory.exists_emWeil_index_horizon_test

#print axioms GaloisForLFunctions.EffectiveArithmeticHodgeTheory.exists_emWeil_index_horizon_certificate
