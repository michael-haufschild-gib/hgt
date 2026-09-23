import GaloisForLFunctions.HTGeometry.GaussQuadrature
import GaloisForLFunctions.HTGeometry.FiniteOrthogonalMomentPolynomials

/-!
# Gaussian quadrature from one finite positive moment block

Gaussian quadrature at level `n` only uses moment positivity through degree `n+1`.  This file
localizes real-rootedness, Christoffel--Darboux, positive Christoffel weights, interpolation, and
degree-`2n+1` exactness to `PositiveMomentFormBelow s N` with `n+1 < N`.

It also identifies the first unseen degree: for every polynomial of degree at most `2n+2`, the
quadrature defect is its top coefficient times the squared norm of `P_(n+1)`.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-! ## Finite-block real and simple roots -/

theorem monicOrtho_aeval_ne_zero_below {N n : ℕ}
    (h : PositiveMomentFormBelow s N) (hnN : n + 1 < N) {z : ℂ} (hz : z.im ≠ 0) :
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
  have hpoly : conjQuadratic z * g * g = A * A + (z.im ^ (2 : ℕ)) • (g * g) := by
    simp only [conjQuadratic, A, Polynomial.smul_eq_C_mul]
    ring
  have hexp : momentInner s (monicOrtho s (n + 1)) g =
      momentInner s A A + z.im ^ (2 : ℕ) * momentInner s g g := by
    rw [hQg, momentInner_def, hpoly, momentFunctional_add, momentFunctional_smul,
      momentInner_def, momentInner_def]
  have hApos : 0 < momentInner s A A := h.self_pos hAne hAN
  have hgpos : 0 < momentInner s g g := h.self_pos hgne hgN
  have himpos : 0 < z.im ^ (2 : ℕ) := sq_pos_of_ne_zero hz
  rw [hexp] at hzero
  nlinarith

theorem monicOrtho_root_im_eq_zero_below {N n : ℕ}
    (h : PositiveMomentFormBelow s N) (hnN : n + 1 < N) {z : ℂ}
    (hz : Polynomial.aeval z (monicOrtho s (n + 1)) = 0) : z.im = 0 := by
  by_contra hne
  exact monicOrtho_aeval_ne_zero_below h hnN hne hz

theorem monicOrtho_splits_below {N n : ℕ}
    (h : PositiveMomentFormBelow s N) (hnN : n + 1 < N) :
    (monicOrtho s (n + 1)).Splits :=
  splits_of_forall_aeval_im_eq_zero (monicOrtho s (n + 1)).natDegree
    (monicOrtho s (n + 1)) le_rfl fun _ hz =>
      monicOrtho_root_im_eq_zero_below h hnN hz

theorem monicOrtho_not_sq_dvd_below {N n : ℕ}
    (h : PositiveMomentFormBelow s N) (hnN : n + 1 < N) (r : ℝ) :
    ¬ (((X - C r) ^ (2 : ℕ) : Polynomial ℝ) ∣ monicOrtho s (n + 1)) := by
  rintro ⟨g, hg⟩
  have hsqne : ((X - C r) ^ (2 : ℕ) : Polynomial ℝ) ≠ 0 :=
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

theorem monicOrtho_roots_nodup_below {N n : ℕ}
    (h : PositiveMomentFormBelow s N) (hnN : n + 1 < N) :
    (monicOrtho s (n + 1)).roots.Nodup := by
  classical
  rw [Multiset.nodup_iff_count_le_one]
  intro r
  rw [count_roots]
  by_contra hc
  have hc2 : 2 ≤ rootMultiplicity r (monicOrtho s (n + 1)) := not_le.mp hc
  exact monicOrtho_not_sq_dvd_below h hnN r
    (dvd_trans (pow_dvd_pow _ hc2) (pow_rootMultiplicity_dvd _ _))

theorem gaussNodes_card_below {N : ℕ}
    (h : PositiveMomentFormBelow s N) (n : ℕ) (hnN : n + 1 < N) :
    (gaussNodes s n).card = n + 1 := by
  classical
  rw [gaussNodes,
    Multiset.toFinset_card_of_nodup (monicOrtho_roots_nodup_below h hnN)]
  rw [← (monicOrtho_splits_below h hnN).natDegree_eq_card_roots]
  exact natDegree_monicOrtho_eq s (n + 1)

/-! ## Finite-block Christoffel kernel -/

theorem momentInner_cdKernel_below {N : ℕ}
    (h : PositiveMomentFormBelow s N) (n : ℕ) (hnN : n + 1 ≤ N)
    (x : ℝ) (p : Polynomial ℝ)
    (hp : p.degree < ((n + 1 : ℕ) : WithBot ℕ)) :
    momentInner s p (cdKernel s n x) = p.eval x := by
  have hexp := monicOrtho_expansion_below h hnN p hp
  rw [cdKernel, momentInner_sum_right]
  simp only [momentInner_smul_right]
  conv_rhs => rw [hexp]
  rw [Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.eval_smul, smul_eq_mul, momentInner_comm]
  ring

theorem cdKernel_eval_self_pos_below {N : ℕ}
    (h : PositiveMomentFormBelow s N) (n : ℕ) (hnN : n < N) (x : ℝ) :
    0 < (cdKernel s n x).eval x := by
  rw [cdKernel_eval_self]
  have hpos : ∀ k < n + 1,
      0 < momentInner s (monicOrtho s k) (monicOrtho s k) := by
    intro k hk
    exact monicOrtho_inner_self_pos_below h (by omega)
  refine Finset.sum_pos' (fun k hk =>
    div_nonneg (sq_nonneg _) (hpos k (Finset.mem_range.mp hk)).le) ⟨0, ?_, ?_⟩
  · exact Finset.mem_range.mpr (Nat.succ_pos n)
  · have h0 : (monicOrtho s 0).eval x = 1 := by simp
    rw [h0]
    exact div_pos (by norm_num) (hpos 0 (Nat.succ_pos n))

theorem christoffel_pos_below {N : ℕ}
    (h : PositiveMomentFormBelow s N) (n : ℕ) (hnN : n < N) (x : ℝ) :
    0 < christoffel s n x :=
  inv_pos.mpr (cdKernel_eval_self_pos_below h n hnN x)

theorem christoffel_mul_cdKernel_below {N : ℕ}
    (h : PositiveMomentFormBelow s N) (n : ℕ) (hnN : n < N) (x : ℝ) :
    christoffel s n x * (cdKernel s n x).eval x = 1 :=
  inv_mul_cancel₀ (ne_of_gt (cdKernel_eval_self_pos_below h n hnN x))

theorem normalisedKernel_eval_self_below {N : ℕ}
    (h : PositiveMomentFormBelow s N) (n : ℕ) (hnN : n < N) (x : ℝ) :
    (christoffel s n x • cdKernel s n x).eval x = 1 := by
  rw [Polynomial.eval_smul, smul_eq_mul]
  exact christoffel_mul_cdKernel_below h n hnN x

/-! ## Finite-block Christoffel--Darboux -/

theorem monicOrtho_three_term_eval_below {N n : ℕ}
    (h : PositiveMomentFormBelow s N) (hnN : n + 2 ≤ N) (x : ℝ) :
    x * (monicOrtho s (n + 1)).eval x =
      (monicOrtho s (n + 2)).eval x
        + (momentInner s (X * monicOrtho s (n + 1)) (monicOrtho s (n + 1)) /
            momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1))) *
              (monicOrtho s (n + 1)).eval x
        + (momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)) /
            momentInner s (monicOrtho s n) (monicOrtho s n)) *
              (monicOrtho s n).eval x := by
  have hev := congrArg (Polynomial.eval x) (monicOrtho_three_term_below h hnN)
  simpa [Polynomial.eval_smul, smul_eq_mul] using hev

theorem christoffelDarboux_below {N : ℕ}
    (h : PositiveMomentFormBelow s N) : ∀ (n : ℕ), n + 1 < N → ∀ x y : ℝ,
    (x - y) * ∑ k ∈ Finset.range (n + 1),
        (monicOrtho s k).eval x * (monicOrtho s k).eval y /
          momentInner s (monicOrtho s k) (monicOrtho s k) =
      ((monicOrtho s (n + 1)).eval x * (monicOrtho s n).eval y -
          (monicOrtho s n).eval x * (monicOrtho s (n + 1)).eval y) /
        momentInner s (monicOrtho s n) (monicOrtho s n) := by
  intro n
  induction n with
  | zero =>
      intro hnN x y
      have h0 : momentInner s (monicOrtho s 0) (monicOrtho s 0) ≠ 0 :=
        h.self_ne_zero (monicOrtho_ne_zero s 0) (by simp; omega)
      have hx0 : (monicOrtho s 0).eval x = 1 := by simp
      have hy0 : (monicOrtho s 0).eval y = 1 := by simp
      have hone := monicOrtho_one_eval_sub s x y
      simp only [Nat.zero_add, Finset.sum_range_one, hx0, hy0, one_mul, mul_one]
      field_simp
      linarith [hone]
  | succ n ih =>
      intro hnN x y
      have hn : momentInner s (monicOrtho s n) (monicOrtho s n) ≠ 0 :=
        h.self_ne_zero (monicOrtho_ne_zero s n) (by
          rw [natDegree_monicOrtho_eq]
          omega)
      have hn1 : momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)) ≠ 0 :=
        h.self_ne_zero (monicOrtho_ne_zero s (n + 1)) (by
          rw [natDegree_monicOrtho_eq]
          omega)
      have hrx := monicOrtho_three_term_eval_below h (by omega : n + 2 ≤ N) x
      have hry := monicOrtho_three_term_eval_below h (by omega : n + 2 ≤ N) y
      have hex : (monicOrtho s (n + 2)).eval x =
          x * (monicOrtho s (n + 1)).eval x
            - (momentInner s (X * monicOrtho s (n + 1)) (monicOrtho s (n + 1)) /
                momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1))) *
              (monicOrtho s (n + 1)).eval x
            - (momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)) /
                momentInner s (monicOrtho s n) (monicOrtho s n)) *
              (monicOrtho s n).eval x := by
        linear_combination -hrx
      have hey : (monicOrtho s (n + 2)).eval y =
          y * (monicOrtho s (n + 1)).eval y
            - (momentInner s (X * monicOrtho s (n + 1)) (monicOrtho s (n + 1)) /
                momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1))) *
              (monicOrtho s (n + 1)).eval y
            - (momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)) /
                momentInner s (monicOrtho s n) (monicOrtho s n)) *
              (monicOrtho s n).eval y := by
        linear_combination -hry
      rw [Finset.sum_range_succ, mul_add, ih (by omega), hex, hey]
      field_simp
      ring

theorem cdKernel_eval_eq_zero_of_root_ne_below {N : ℕ}
    (h : PositiveMomentFormBelow s N) (n : ℕ) (hnN : n + 1 < N) {x y : ℝ}
    (hx : (monicOrtho s (n + 1)).eval x = 0)
    (hy : (monicOrtho s (n + 1)).eval y = 0) (hxy : x ≠ y) :
    (cdKernel s n x).eval y = 0 := by
  have hcd := christoffelDarboux_below h n hnN x y
  have hzero : ((monicOrtho s (n + 1)).eval x * (monicOrtho s n).eval y -
      (monicOrtho s n).eval x * (monicOrtho s (n + 1)).eval y) /
      momentInner s (monicOrtho s n) (monicOrtho s n) = 0 := by
    rw [hx, hy]
    ring
  rw [hzero] at hcd
  rw [cdKernel_eval]
  rcases mul_eq_zero.mp hcd with h1 | h2
  · exact absurd (sub_eq_zero.mp h1) hxy
  · exact h2

/-! ## Finite-block Gaussian exactness and first defect -/

theorem gaussBasis_eval_of_ne_below {N : ℕ}
    (h : PositiveMomentFormBelow s N) (n : ℕ) (hnN : n + 1 < N) {x y : ℝ}
    (hx : (monicOrtho s (n + 1)).eval x = 0)
    (hy : (monicOrtho s (n + 1)).eval y = 0) (hxy : x ≠ y) :
    (gaussBasis s n x).eval y = 0 := by
  rw [gaussBasis, eval_smul, smul_eq_mul,
    cdKernel_eval_eq_zero_of_root_ne_below h n hnN hx hy hxy, mul_zero]

theorem momentFunctional_gaussBasis_below {N : ℕ}
    (h : PositiveMomentFormBelow s N) (n : ℕ) (hnN : n + 1 ≤ N) (x : ℝ) :
    momentFunctional s (gaussBasis s n x) = christoffel s n x := by
  have hone : (1 : Polynomial ℝ).degree < ((n + 1 : ℕ) : WithBot ℕ) := by
    rw [degree_one]
    exact_mod_cast Nat.succ_pos n
  have hrep : momentInner s 1 (cdKernel s n x) = 1 := by
    simpa using momentInner_cdKernel_below h n hnN x 1 hone
  have hK : momentFunctional s (cdKernel s n x) = 1 := by
    rw [← hrep, momentInner_def, one_mul]
  rw [gaussBasis, momentFunctional_smul, hK, mul_one]

theorem gauss_interpolation_below {N : ℕ}
    (h : PositiveMomentFormBelow s N) (n : ℕ) (hnN : n + 1 < N)
    (p : Polynomial ℝ) (hp : p.degree < ((n + 1 : ℕ) : WithBot ℕ)) :
    p = ∑ x ∈ gaussNodes s n, p.eval x • gaussBasis s n x := by
  classical
  have hsumdeg : (∑ x ∈ gaussNodes s n, p.eval x • gaussBasis s n x).degree
      < ((n + 1 : ℕ) : WithBot ℕ) := by
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr ?_
    intro x _
    exact lt_of_le_of_lt (degree_smul_le _ _) (gaussBasis_degree_lt s n x)
  set D := p - ∑ x ∈ gaussNodes s n, p.eval x • gaussBasis s n x with hDdef
  have hDdeg : D.degree < ((n + 1 : ℕ) : WithBot ℕ) :=
    lt_of_le_of_lt (degree_sub_le _ _) (max_lt hp hsumdeg)
  have hDeval : ∀ y ∈ gaussNodes s n, D.eval y = 0 := by
    intro y hy
    have hyroot : (monicOrtho s (n + 1)).eval y = 0 := (mem_gaussNodes_iff n y).mp hy
    have hsum : ∑ x ∈ gaussNodes s n, (p.eval x • gaussBasis s n x).eval y =
        p.eval y := by
      rw [Finset.sum_eq_single y]
      · rw [gaussBasis, eval_smul, smul_eq_mul,
          normalisedKernel_eval_self_below h n (by omega) y, mul_one]
      · intro x hx hxy
        have hxroot : (monicOrtho s (n + 1)).eval x = 0 :=
          (mem_gaussNodes_iff n x).mp hx
        rw [eval_smul, smul_eq_mul,
          gaussBasis_eval_of_ne_below h n hnN hxroot hyroot hxy, mul_zero]
      · intro hy'
        exact absurd hy hy'
    rw [hDdef, eval_sub, eval_finsetSum, hsum, sub_self]
  have hDzero : D = 0 := by
    by_cases hD0 : D = 0
    · exact hD0
    · refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero' D (gaussNodes s n) hDeval ?_
      rw [gaussNodes_card_below h n hnN]
      exact (natDegree_lt_iff_degree_lt hD0).mpr hDdeg
  rw [hDdef] at hDzero
  exact sub_eq_zero.mp hDzero

theorem momentFunctional_eq_gaussSum_of_degree_lt_below {N : ℕ}
    (h : PositiveMomentFormBelow s N) (n : ℕ) (hnN : n + 1 < N)
    (p : Polynomial ℝ) (hp : p.degree < ((n + 1 : ℕ) : WithBot ℕ)) :
    momentFunctional s p =
      ∑ x ∈ gaussNodes s n, christoffel s n x * p.eval x := by
  conv_lhs => rw [gauss_interpolation_below h n hnN p hp]
  rw [momentFunctional_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [momentFunctional_smul, momentFunctional_gaussBasis_below h n (by omega) x]
  ring

theorem momentFunctional_eq_gaussSum_below {N : ℕ}
    (h : PositiveMomentFormBelow s N) (n : ℕ) (hnN : n + 1 < N)
    (p : Polynomial ℝ) (hp : p.degree < ((2 * n + 2 : ℕ) : WithBot ℕ)) :
    momentFunctional s p =
      ∑ x ∈ gaussNodes s n, christoffel s n x * p.eval x := by
  classical
  have hQm : (monicOrtho s (n + 1)).Monic := monicOrtho_monic s (n + 1)
  have hQnd : (monicOrtho s (n + 1)).natDegree = n + 1 :=
    natDegree_monicOrtho_eq s (n + 1)
  have hsplit : p %ₘ monicOrtho s (n + 1) +
      monicOrtho s (n + 1) * (p /ₘ monicOrtho s (n + 1)) = p :=
    modByMonic_add_div p (monicOrtho s (n + 1))
  set q := p /ₘ monicOrtho s (n + 1) with hqdef
  set r := p %ₘ monicOrtho s (n + 1) with hrdef
  have hrdeg : r.degree < ((n + 1 : ℕ) : WithBot ℕ) := by
    have hlt := degree_modByMonic_lt p hQm
    rw [monicOrtho_degree s (n + 1)] at hlt
    exact hlt
  have hqdeg : q.degree < ((n + 1 : ℕ) : WithBot ℕ) := by
    by_cases hq0 : q = 0
    · rw [hq0, degree_zero]
      exact WithBot.bot_lt_coe _
    · have hp0 : p ≠ 0 := by
        intro hpz
        refine hq0 ?_
        rw [hqdef, hpz]
        simp
      have hnd : q.natDegree = p.natDegree - (n + 1) := by
        rw [hqdef, natDegree_divByMonic p hQm, hQnd]
      have hpnd : p.natDegree < 2 * n + 2 :=
        (natDegree_lt_iff_degree_lt hp0).mpr hp
      refine (natDegree_lt_iff_degree_lt hq0).mp ?_
      omega
  have horth : momentFunctional s (monicOrtho s (n + 1) * q) = 0 := by
    have hz := monicOrtho_inner_eq_zero_of_degree_lt_below
      (p := q) h (by omega : n + 1 ≤ N) hqdeg
    rwa [momentInner_def] at hz
  rw [← hsplit, momentFunctional_add, horth, add_zero,
    momentFunctional_eq_gaussSum_of_degree_lt_below h n hnN r hrdeg]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hxroot : (monicOrtho s (n + 1)).eval x = 0 := (mem_gaussNodes_iff n x).mp hx
  rw [eval_add, eval_mul, hxroot, zero_mul, add_zero]

/-- **First Gaussian defect.** One degree beyond exactness, the entire observer loss is the top
coefficient times the next monic norm. -/
theorem momentFunctional_sub_gaussSum_eq_topCoeff_mul_nextNorm_below {N : ℕ}
    (h : PositiveMomentFormBelow s N) (n : ℕ) (hnN : n + 1 < N)
    (p : Polynomial ℝ) (hp : p.degree < ((2 * n + 3 : ℕ) : WithBot ℕ)) :
    momentFunctional s p -
        ∑ x ∈ gaussNodes s n, christoffel s n x * p.eval x =
      p.coeff (2 * n + 2) *
        momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)) := by
  classical
  let Q : Polynomial ℝ := monicOrtho s (n + 1)
  let a : ℝ := p.coeff (2 * n + 2)
  let r : Polynomial ℝ := p - a • Q ^ (2 : ℕ)
  have hQnat : Q.natDegree = n + 1 := by
    exact natDegree_monicOrtho_eq s (n + 1)
  have hQsqnat : (Q ^ (2 : ℕ)).natDegree = 2 * n + 2 := by
    rw [natDegree_pow, hQnat]
    omega
  have hQsqcoeff : (Q ^ (2 : ℕ)).coeff (2 * n + 2) = 1 := by
    rw [← hQsqnat]
    exact ((monicOrtho_monic s (n + 1)).pow 2).coeff_natDegree
  have hrdeg : r.degree < ((2 * n + 2 : ℕ) : WithBot ℕ) := by
    rw [degree_lt_iff_coeff_zero]
    intro k hk
    rcases eq_or_lt_of_le hk with rfl | hkgt
    · simp [r, a, hQsqcoeff, smul_eq_mul]
    · have hpzero : p.coeff k = 0 := by
        apply coeff_eq_zero_of_degree_lt
        exact lt_of_lt_of_le hp (by exact_mod_cast (show 2 * n + 3 ≤ k by omega))
      have hQzero : (Q ^ (2 : ℕ)).coeff k = 0 :=
        coeff_eq_zero_of_natDegree_lt (by rw [hQsqnat]; exact hkgt)
      simp [r, hpzero, hQzero]
  have hrquad := momentFunctional_eq_gaussSum_below h n hnN r hrdeg
  have hQeval : ∀ x ∈ gaussNodes s n, (Q ^ (2 : ℕ)).eval x = 0 := by
    intro x hx
    have hxroot : Q.eval x = 0 := (mem_gaussNodes_iff n x).mp hx
    rw [eval_pow, hxroot, zero_pow]
    norm_num
  have hQmoment : momentFunctional s (Q ^ (2 : ℕ)) = momentInner s Q Q := by
    rw [pow_two, momentInner_def]
  have hrmoment : momentFunctional s r =
      momentFunctional s p - a * momentFunctional s (Q ^ (2 : ℕ)) := by
    change momentFunctional s (p - a • Q ^ (2 : ℕ)) =
      momentFunctional s p - a * momentFunctional s (Q ^ (2 : ℕ))
    rw [sub_eq_add_neg, momentFunctional_add]
    rw [show -(a • Q ^ (2 : ℕ)) = (-a) • Q ^ (2 : ℕ) by simp,
      momentFunctional_smul]
    ring
  have hrsum :
      (∑ x ∈ gaussNodes s n, christoffel s n x * r.eval x) =
        ∑ x ∈ gaussNodes s n, christoffel s n x * p.eval x := by
    apply Finset.sum_congr rfl
    intro x hx
    change christoffel s n x * (p - a • Q ^ (2 : ℕ)).eval x =
      christoffel s n x * p.eval x
    rw [eval_sub, eval_smul, smul_eq_mul, hQeval x hx]
    ring
  rw [hrmoment, hrsum, hQmoment] at hrquad
  linarith

end HTGeometry
