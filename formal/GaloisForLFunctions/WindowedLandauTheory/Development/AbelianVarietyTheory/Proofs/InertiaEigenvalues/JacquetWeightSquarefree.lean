import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetDerivativeTrace
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalDerivativeMackey
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetPatternEndpoints
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerJacquetIdempotents
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerMultiplicityOne
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraWeightNonneg

/-! For a squarefree label, the weighted derivative count bounds the
Jacquet series weight by the Whittaker weight times `(1+1/g)^n`. -/

noncomputable section
open GaloisForLFunctions Polynomial WindowedLandauTheory.MainNotions.ArithmeticCylinders
open scoped Classical

namespace GlobalTheory.GLq

variable {g n k b : ℕ} [Fact g.Prime]

omit [Fact g.Prime] in
private theorem sum_get_rank (L : List (Pc g)) :
    (∑ j : Fin L.length, (L.get j).1) = degL L := by
  exact Fin.sum_univ_fun_getElem L (fun p => p.1)

private theorem tr_eJ'_re_le_cuspidalList (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1)
    (L : List (Pc g)) (hL : degL L = k + 1 + b) (hcus : ∀ p ∈ L, IsCusp p.2 ∧ wh ψ p.2 = 1) :
    (tr (eJ' g (k + 1 + b) k ψ) (hcL L (k + 1 + b))).re ≤
      (g : ℝ) ^ k * (1 + 1 / (g : ℝ)) ^ (k + 1 + b) := by
  let χ := hcL L (k + 1 + b)
  let r (j : Fin L.length) := (L.get j).1
  let q : ℝ := g
  have hq : 1 ≤ q := by
    change (1 : ℝ) ≤ (g : ℝ)
    exact_mod_cast (Fact.out : g.Prime).one_le
  have hχ : IsClass χ := by
    have h : IsChar χ := by
      change IsChar (hcL L (k + 1 + b))
      rw [← hL]
      exact isChar_hcL L fun p hp => isChar_of_cuspidal (hcus p hp).1
    obtain ⟨V, hV⟩ := h
    exact fun x y => (hV _).symm.trans ((V.char_conj x y).trans (hV x))
  have hder (i : ℕ) (hi : i ≤ k + 1 + b) :
      (wh ψ (der ψ i χ)).re ≤ (subsetRankCount r i : ℝ) := by
    change (wh ψ (der ψ i (hcL L (k + 1 + b)))).re ≤ _
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hi
    rw [hd]
    exact wh_der_hcL_re_le_subsetRankCount ψ hψ L (hL.trans hd) hcus
  let c (i : ℕ) := (subsetRankCount r i : ℝ) * (q ^ (k - i) - q ^ (k - i - 1))
  have hterm (i : Fin k) :
      (wh ψ (der ψ (i : ℕ) χ) * wh ψ (gg ψ (k - (i : ℕ)))).re ≤ c i := by
    have hi := i.isLt
    have hd : 0 < k - (i : ℕ) := by omega
    rw [wh_gg_eq_real ψ hψ, if_neg hd.ne', mul_comm, Complex.re_ofReal_mul]
    change (q ^ (k - (i : ℕ)) - q ^ (k - (i : ℕ) - 1)) * (wh ψ (der ψ (i : ℕ) χ)).re ≤
      (subsetRankCount r i : ℝ) * (q ^ (k - (i : ℕ)) - q ^ (k - (i : ℕ) - 1))
    rw [mul_comm (q ^ (k - (i : ℕ)) - q ^ (k - (i : ℕ) - 1))]
    exact mul_le_mul_of_nonneg_right (hder i (by omega))
      (sub_nonneg.mpr (pow_le_pow_right₀ hq (Nat.sub_le _ _)))
  have hlast : (wh ψ (der ψ k χ) * wh ψ (gg ψ (k - k))).re ≤ (subsetRankCount r k : ℝ) := by
    rw [Nat.sub_self, gg_zero ψ, wh_rank_zero ψ (fun _ => 1), mul_one]
    exact hder k (by omega)
  rw [tr_eJ'_eq_sum_wh_der ψ hψ χ hχ]
  change Complex.reAddGroupHom (∑ i : Fin (k + 1), wh ψ (der ψ i.val χ) *
    wh ψ (gg ψ (k - i.val))) ≤ _
  rw [map_sum, Fin.sum_univ_castSucc]
  calc
    _ ≤ (∑ i : Fin k, c i) + (subsetRankCount r k : ℝ) :=
      add_le_add (Finset.sum_le_sum fun i _ => hterm i) hlast
    _ ≤ _ := by
      rw [Fin.sum_univ_eq_sum_range c k]
      have h := subsetRankCount_weighted_le r (fun j => (hcus _ (List.get_mem L j)).1.1) hq k
      rw [show (∑ j, r j) = k + 1 + b from (sum_get_rank L).trans hL] at h
      exact h

/-- The Jacquet weight of a squarefree label is at most the normalized
weighted subset bound times its Whittaker weight. -/
theorem wtC_eJ_upper_squarefree (L : LabelDatum g) (hg : 5 ≤ g)
    (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (k s : ℕ) (hn : n = k + 2 * s + 1)
    (f : (ZMod g)[X]) (hm : f.Monic) (hd : f.natDegree = n)
    (h0 : f.coeff 0 ≠ 0) (hs : Squarefree f) :
    wtC L (eJ g n k s ψ) f ≤ (1 + 1 / (g : ℝ)) ^ n * wtC L (eU g n ψ) f := by
  obtain ⟨Q, hQ, _, hQd, hser⟩ := squarefree_label_series L hg f hm hd h0 hs
  let T := Q.map Prod.snd
  let χ := hcL T n
  have hχ : IsIrr χ := by
    have h : χ ∈ {η : Gn g n → ℂ | IsIrr η ∧ HasLabel L η f} := by
      rw [hser]
      exact Set.mem_singleton _
    exact h.1
  have hcus (p : Pc g) (hp : p ∈ T) : IsCusp p.2 := by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact (hQ q hq).1.2.1
  have hwh (p : Pc g) (hp : p ∈ T) : IsCusp p.2 ∧ wh ψ p.2 = 1 := by
    have h := hcus p hp
    exact ⟨h, wh_eq_one_of_generic L hg h.1 ψ hψ h.2.1 (wh_std_ne_zero_of_cuspidal h)⟩
  have hU : tr (eU g n ψ) χ = 1 := by
    change wh ψ χ = 1
    apply wh_eq_one_of_generic L hg (by omega) ψ hψ hχ
    change wh ZMod.stdAddChar (hcL T n) ≠ 0
    rw [← hQd]
    exact wh_hcL_ne_zero_of_cusp T hcus
  let q : ℝ := g
  let c : ℝ := (q ^ (n * (n - 1) / 2))⁻¹
  let K : ℝ := (1 + 1 / q) ^ n
  have hcl : IsClass χ := by
    obtain ⟨V, _, hV⟩ := hχ
    exact fun x y => (hV _).symm.trans ((V.char_conj x y).trans (hV x))
  have htr : (tr (eJ g n k s ψ) χ).re ≤ q ^ k * K := by
    rw [JacquetPattern.tr_eJ_eq_tr_eJ' ψ hψ k s hn χ hcl]
    obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le (show k + 1 ≤ n by omega)
    exact tr_eJ'_re_le_cuspidalList ψ hψ T hQd hwh
  have he : eSerC L n f = zOf χ := by
    unfold eSerC
    rw [hser, finsum_mem_singleton]
  obtain ⟨d, hdpos, hχd⟩ := irr_degree_pos hχ
  let t : ℝ := (d : ℝ) / (Fintype.card (Gn g n) : ℝ)
  have ht : χ 1 / (Fintype.card (Gn g n) : ℂ) = (t : ℂ) := by
    simp only [t, hχd, Complex.ofReal_div, Complex.ofReal_natCast]
  have hq : 0 < q := Nat.cast_pos.mpr (Fact.out : g.Prime).pos
  have hqk := pow_pos hq k
  have hc : 0 < c := inv_pos.mpr (pow_pos hq _)
  have hcoefU : ((eU g n ψ).coeff 1).re = c := by
    rw [(eU_mul_self_coeff_one (n := n) ψ).2]
    simp only [c, q, ← Complex.ofReal_natCast g, ← Complex.ofReal_pow, ← Complex.ofReal_inv,
      Complex.ofReal_re]
  have hcoefJ : ((eJ g n k s ψ).coeff 1).re = q ^ k * c := by
    rw [(eJ_mul_self_coeff_one ψ k s (by omega : s + k < n)).2]
    simp only [c, q, ← Complex.ofReal_natCast g, ← Complex.ofReal_pow, ← Complex.ofReal_inv,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [wtC, wtC, he, coeff_one_mul_zOf, coeff_one_mul_zOf, ht, hU, mul_one,
    Complex.re_ofReal_mul, Complex.ofReal_re, hcoefU, hcoefJ]
  change t * (tr (eJ g n k s ψ) χ).re / (q ^ k * c) ≤ K * (t / c)
  calc
    _ ≤ t * (q ^ k * K) / (q ^ k * c) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left htr (by positivity)) (mul_nonneg hqk.le hc.le)
    _ = _ := by field_simp [hqk.ne', hc.ne']

end GlobalTheory.GLq
