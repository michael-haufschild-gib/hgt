import GaloisForLFunctions.HTGeometry.FiniteGaussQuadrature
import GaloisForLFunctions.HTGeometry.MonicMomentAdmission
import GaloisForLFunctions.HTGeometry.HankelSuccessorSchur

/-! # Real roots and the signed minimum at a finite Hankel cutoff

A positive `N × N` moment section determines a monic degree-`N` orthogonal
polynomial. Its roots are simple and real, and it strictly minimizes the signed
squared norm among monic polynomials of that degree. Its minimum is exactly the
successor Schur coordinate, whose sign is not assumed.
-/

open scoped BigOperators
open Polynomial
namespace HTGeometry
variable {s : ℕ → ℝ}

theorem monicOrtho_aeval_ne_zero_at_cutoff {N n : ℕ}
    (h : PositiveMomentFormBelow s N) (hnN : n + 1 ≤ N) {z : ℂ} (hz : z.im ≠ 0) :
    Polynomial.aeval z (monicOrtho s (n + 1)) ≠ 0 := by
  intro hQ
  obtain ⟨g, hQg⟩ :=
    conjQuadratic_dvd_of_aeval_eq_zero (monicOrtho s (n + 1)) hz hQ
  have hgne : g ≠ 0 := by
    intro hg0
    rw [hg0, mul_zero] at hQg
    exact monicOrtho_ne_zero s (n + 1) hQg
  have hnd : (monicOrtho s (n + 1)).natDegree = 2 + g.natDegree := by
    rw [hQg, natDegree_mul (conjQuadratic_ne_zero z) hgne, conjQuadratic_natDegree]
  have hQnd : (monicOrtho s (n + 1)).natDegree = n + 1 :=
    natDegree_monicOrtho_eq s (n + 1)
  have hglt : g.natDegree < n + 1 := by omega
  have hgdeg : g.degree < ((n + 1 : ℕ) : WithBot ℕ) := by
    rw [degree_eq_natDegree hgne]
    exact_mod_cast hglt
  have hzero : momentInner s (monicOrtho s (n + 1)) g = 0 :=
    monicOrtho_inner_eq_zero_of_degree_lt_below h (by omega) hgdeg
  let A : Polynomial ℝ := (X - C z.re) * g
  have hAne : A ≠ 0 := mul_ne_zero (X_sub_C_ne_zero z.re) hgne
  have hgN : g.natDegree < N := by omega
  have hAN : A.natDegree < N := by
    dsimp only [A]
    refine lt_of_le_of_lt Polynomial.natDegree_mul_le ?_
    simp only [natDegree_X_sub_C]
    omega
  have hpoly : conjQuadratic z * g * g = A * A + (z.im ^ 2) • (g * g) := by
    simp only [conjQuadratic, A, Polynomial.smul_eq_C_mul]
    ring
  have hexp : momentInner s (monicOrtho s (n + 1)) g =
      momentInner s A A + z.im ^ 2 * momentInner s g g := by
    rw [hQg, momentInner_def, hpoly, momentFunctional_add, momentFunctional_smul,
      momentInner_def, momentInner_def]
  have hApos : 0 < momentInner s A A := h.self_pos hAne hAN
  have hgpos : 0 < momentInner s g g := h.self_pos hgne hgN
  have himpos : 0 < z.im ^ 2 := sq_pos_of_ne_zero hz
  rw [hexp] at hzero
  nlinarith

theorem monicOrtho_root_im_eq_zero_at_cutoff {N n : ℕ}
    (h : PositiveMomentFormBelow s N) (hnN : n + 1 ≤ N) {z : ℂ}
    (hz : Polynomial.aeval z (monicOrtho s (n + 1)) = 0) : z.im = 0 := by
  by_contra hne
  exact monicOrtho_aeval_ne_zero_at_cutoff h hnN hne hz

theorem monicOrtho_splits_at_cutoff {N n : ℕ}
    (h : PositiveMomentFormBelow s N) (hnN : n + 1 ≤ N) :
    (monicOrtho s (n + 1)).Splits :=
  splits_of_forall_aeval_im_eq_zero (monicOrtho s (n + 1)).natDegree
    (monicOrtho s (n + 1)) le_rfl fun _ hz =>
      monicOrtho_root_im_eq_zero_at_cutoff h hnN hz

theorem monicOrtho_not_sq_dvd_at_cutoff {N n : ℕ}
    (h : PositiveMomentFormBelow s N) (hnN : n + 1 ≤ N) (r : ℝ) :
    ¬ (((X - C r) ^ 2 : Polynomial ℝ) ∣ monicOrtho s (n + 1)) := by
  rintro ⟨g, hg⟩
  have hsqne : ((X - C r) ^ 2 : Polynomial ℝ) ≠ 0 :=
    pow_ne_zero 2 (X_sub_C_ne_zero r)
  have hgne : g ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hg
    exact monicOrtho_ne_zero s (n + 1) hg
  have hnd : (monicOrtho s (n + 1)).natDegree = 2 + g.natDegree := by
    rw [hg, natDegree_mul hsqne hgne, natDegree_pow, natDegree_X_sub_C]
  have hQnd : (monicOrtho s (n + 1)).natDegree = n + 1 :=
    natDegree_monicOrtho_eq s (n + 1)
  have hglt : g.natDegree < n + 1 := by omega
  have hgdeg : g.degree < ((n + 1 : ℕ) : WithBot ℕ) := by
    rw [degree_eq_natDegree hgne]
    exact_mod_cast hglt
  have hzero : momentInner s (monicOrtho s (n + 1)) g = 0 :=
    monicOrtho_inner_eq_zero_of_degree_lt_below h (by omega) hgdeg
  let A : Polynomial ℝ := (X - C r) * g
  have hAne : A ≠ 0 := mul_ne_zero (X_sub_C_ne_zero r) hgne
  have hAN : A.natDegree < N := by
    dsimp only [A]
    refine lt_of_le_of_lt Polynomial.natDegree_mul_le ?_
    simp only [natDegree_X_sub_C]
    omega
  have hexp : momentInner s (monicOrtho s (n + 1)) g = momentInner s A A := by
    rw [hg, momentInner_def, momentInner_def]
    dsimp only [A]
    ring_nf
  rw [hexp] at hzero
  exact (ne_of_gt (h.self_pos hAne hAN)) hzero

theorem monicOrtho_roots_nodup_at_cutoff {N n : ℕ}
    (h : PositiveMomentFormBelow s N) (hnN : n + 1 ≤ N) :
    (monicOrtho s (n + 1)).roots.Nodup := by
  classical
  rw [Multiset.nodup_iff_count_le_one]
  intro r
  rw [count_roots]
  by_contra hc
  have hc2 : 2 ≤ rootMultiplicity r (monicOrtho s (n + 1)) := not_le.mp hc
  exact monicOrtho_not_sq_dvd_at_cutoff h hnN r
    (dvd_trans (pow_dvd_pow _ hc2) (pow_rootMultiplicity_dvd _ _))

theorem gaussNodes_card_at_cutoff {N : ℕ}
    (h : PositiveMomentFormBelow s N) (n : ℕ) (hnN : n + 1 ≤ N) :
    (gaussNodes s n).card = n + 1 := by
  classical
  rw [gaussNodes,
    Multiset.toFinset_card_of_nodup (monicOrtho_roots_nodup_at_cutoff h hnN)]
  rw [← (monicOrtho_splits_at_cutoff h hnN).natDegree_eq_card_roots]
  exact natDegree_monicOrtho_eq s (n + 1)


/-- At the finite cutoff, subtracting the monic orthogonal polynomial leaves a
lower-degree polynomial whose signed squared norm is strictly positive unless it is zero. -/
theorem monicOrtho_cutoff_norm_decomposition {N : ℕ}
    (h : PositiveMomentFormBelow s N) {p : Polynomial ℝ}
    (hp : p.Monic) (hdeg : p.natDegree = N) :
    momentInner s p p =
      momentInner s (monicOrtho s N) (monicOrtho s N) +
        momentInner s (p - monicOrtho s N) (p - monicOrtho s N) := by
  have hdeq : p.degree = (monicOrtho s N).degree := by
    rw [degree_eq_natDegree hp.ne_zero, hdeg, monicOrtho_degree]
  have hlc : p.leadingCoeff = (monicOrtho s N).leadingCoeff := by
    rw [hp.leadingCoeff, (monicOrtho_monic s N).leadingCoeff]
  have hrdeg : (p - monicOrtho s N).degree < (N : WithBot ℕ) := by
    have hh := Polynomial.degree_sub_lt hdeq hp.ne_zero hlc
    rwa [degree_eq_natDegree hp.ne_zero, hdeg] at hh
  have hz := monicOrtho_inner_eq_zero_of_degree_lt_below h le_rfl hrdeg
  have hzp : momentInner s (monicOrtho s N) p =
      momentInner s (monicOrtho s N) (monicOrtho s N) := by
    rw [momentInner_sub_right] at hz
    linarith
  rw [momentInner_sub_left, momentInner_sub_right, momentInner_sub_right,
    momentInner_comm s p (monicOrtho s N), hzp]
  ring

/-- The cutoff polynomial is the strict minimizer among monic polynomials of
its degree, even when its own signed squared norm is not known nonnegative. -/
theorem monicOrtho_cutoff_norm_lt {N : ℕ}
    (h : PositiveMomentFormBelow s N) {p : Polynomial ℝ}
    (hp : p.Monic) (hdeg : p.natDegree = N) (hne : p ≠ monicOrtho s N) :
    momentInner s (monicOrtho s N) (monicOrtho s N) < momentInner s p p := by
  have hrne : p - monicOrtho s N ≠ 0 := sub_ne_zero.mpr hne
  have hdeq : p.degree = (monicOrtho s N).degree := by
    rw [degree_eq_natDegree hp.ne_zero, hdeg, monicOrtho_degree]
  have hlc : p.leadingCoeff = (monicOrtho s N).leadingCoeff := by
    rw [hp.leadingCoeff, (monicOrtho_monic s N).leadingCoeff]
  have hrdeg : (p - monicOrtho s N).natDegree < N := by
    have hh := Polynomial.degree_sub_lt hdeq hp.ne_zero hlc
    rw [degree_eq_natDegree hrne, degree_eq_natDegree hp.ne_zero, hdeg] at hh
    exact_mod_cast hh
  rw [monicOrtho_cutoff_norm_decomposition h hp hdeg]
  exact lt_add_of_pos_right _ (h.self_pos hrne hrdeg)

/-- The signed squared norm of the cutoff orthogonal polynomial is exactly the
successor Schur coordinate. Only the preceding Hankel section is assumed positive. -/
theorem monicOrtho_cutoff_norm_eq_schur {n : ℕ}
    (hhead : (momentHankelMatrix s n).PosDef) :
    momentInner s (monicOrtho s n) (monicOrtho s n) =
      GaloisForLFunctions.HTGeometry.finiteHankelSuccessorSchur s n := by
  have h := positiveMomentFormBelow_of_hankelPosDef hhead
  have heq : monicOrtho s n = monicMomentAdmissionPolynomial s n := by
    apply eq_monicMomentAdmissionPolynomial_of_monic_of_orthogonal
      hhead.det_pos.ne' (monicOrtho_monic s n) (natDegree_monicOrtho_eq s n)
    intro i
    change momentInner s (X ^ (i : ℕ)) (monicOrtho s n) = 0
    rw [momentInner_comm]
    apply monicOrtho_inner_eq_zero_of_degree_lt_below h le_rfl
    rw [degree_X_pow]
    exact_mod_cast i.isLt
  have hform := heq.trans (monicMomentAdmissionPolynomial_eq s n)
  have hzero : momentInner s (monicOrtho s n)
      (Polynomial.ofFn n (monicMomentAdmissionCoefficients s n)) = 0 :=
    monicOrtho_inner_eq_zero_of_degree_lt_below h le_rfl (Polynomial.ofFn_degree_lt _)
  have hnorm := congrArg (fun p => momentInner s (monicOrtho s n) p) hform
  rw [momentInner_add_right, hzero, add_zero] at hnorm
  calc
    momentInner s (monicOrtho s n) (monicOrtho s n) =
        momentInner s (X ^ n) (monicOrtho s n) := by
      rw [hnorm, momentInner_comm]
    _ = s (n + n) + ∑ i : Fin n,
        monicMomentAdmissionCoefficients s n i * s (n + (i : ℕ)) := by
      rw [hform, momentInner_add_right, momentInner_def, momentInner_def,
        ← pow_add, momentFunctional_X_pow, momentFunctional_X_pow_mul_ofFn]
    _ = GaloisForLFunctions.HTGeometry.finiteHankelSuccessorSchur s n := by
      have hmat : momentHankelMatrix s n =
          GaloisForLFunctions.HTGeometry.finiteHankelMatrix s n := rfl
      simp only [monicMomentAdmissionCoefficients, hmat, Pi.neg_apply,
        Matrix.mulVec, dotProduct, momentHankelTail, neg_mul, Finset.sum_mul,
        Finset.sum_neg_distrib,
        GaloisForLFunctions.HTGeometry.finiteHankelSuccessorSchur]
      rw [show n + n = 2 * n by omega, ← sub_eq_add_neg]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [Nat.add_comm n (i : ℕ)]
      ring

end HTGeometry
