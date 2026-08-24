import GaloisForLFunctions.RHTower.VisibleCoprimeZetaZeroJet
import GaloisForLFunctions.RHTower.ChenGuptaLiPrimitiveClassIContours
import GaloisForLFunctions.HTGeometry.AnalyticConjReflection
import GaloisForLFunctions.RHTower.EntireWeightedLittlewoodRectangle
import GaloisForLFunctions.RHTower.GelfondSchneiderProof.AnalyticPart

/-!
# Visible-coprime primitive Dirichlet zero jets

For a character `chi` modulo `N`, the primitive-lattice Mellin symbol on the
absolute-convergence chamber is

`L(s, chi) * L(t, chi⁻¹) / L(s+t, 1)`.

This file proves that identity directly from the positive Dirichlet series,
constructs the pole-filled principal reciprocal, and continues the numerator
kernel holomorphically.  At every actual open-strip zero of a primitive,
nonprincipal character, the exact mixed jet is the norm-square of the leading
`L`-jet times that principal reciprocal.  Its sign is negative left of the
critical line, zero exactly on it, and positive right of it.  These are the
unconditional primitive-character laws `(V10)`--`(V12)` from the
visible-coprime zero-jet card; no GRH, simplicity, or zero-location premise is
used by the capstones.
-/

open Complex LSeries DirichletCharacter Filter Topology

namespace RHTower

noncomputable section

theorem LFunction_principal_mod_one_eq_riemannZeta (s : ℂ) :
    DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) s = riemannZeta s := by
  rw [DirichletCharacter.LFunction, ZMod.LFunction]
  simp only [Nat.cast_one, one_cpow, one_mul, Finset.univ_unique, Finset.sum_singleton]
  change (1 : DirichletCharacter ℂ 1) (0 : ZMod 1) *
      HurwitzZeta.hurwitzZeta (ZMod.toAddCircle (0 : ZMod 1)) s = riemannZeta s
  have hchar : (1 : DirichletCharacter ℂ 1) (0 : ZMod 1) = 1 := by
    rw [show (0 : ZMod 1) = 1 by exact Subsingleton.elim _ _]
    exact map_one _
  have hcircle : ZMod.toAddCircle (0 : ZMod 1) = 0 := map_zero _
  rw [hchar, hcircle, HurwitzZeta.hurwitzZeta_zero, one_mul]

def principalDirichletEulerProduct (N : ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-s))

theorem principalLFunction_eq_zeta_mul_eulerProduct
    (n : ℕ) {s : ℂ} (hs : s ≠ 1) :
    DirichletCharacter.LFunction (1 : DirichletCharacter ℂ (n + 1)) s =
      riemannZeta s * principalDirichletEulerProduct (n + 1) s := by
  have h := DirichletCharacter.LFunction_changeLevel
    (M := 1) (N := n + 1) (one_dvd (n + 1))
    (1 : DirichletCharacter ℂ 1) (s := s) (Or.inr hs)
  rw [DirichletCharacter.changeLevel_one,
    LFunction_principal_mod_one_eq_riemannZeta] at h
  rw [h]
  unfold principalDirichletEulerProduct
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  have hchar : (1 : DirichletCharacter ℂ 1) (p : ZMod 1) = 1 := by
    rw [show (p : ZMod 1) = 1 by exact Subsingleton.elim _ _]
    exact map_one _
  rw [hchar, one_mul]

def principalDirichletInv (N : ℕ) (s : ℂ) : ℂ :=
  Sieve.invZeta s * (principalDirichletEulerProduct N s)⁻¹

theorem principalDirichletInv_eq_inv_LFunction
    (n : ℕ) {s : ℂ} (hs : s ≠ 1) :
    principalDirichletInv (n + 1) s =
      (DirichletCharacter.LFunction
        (1 : DirichletCharacter ℂ (n + 1)) s)⁻¹ := by
  rw [principalDirichletInv, Sieve.invZeta_eq_inv hs,
    principalLFunction_eq_zeta_mul_eulerProduct n hs, mul_inv]

theorem principalDirichletEulerProduct_analyticAt (N : ℕ) (s : ℂ) :
    AnalyticAt ℂ (principalDirichletEulerProduct N) s := by
  unfold principalDirichletEulerProduct
  apply Finset.analyticAt_fun_prod
  intro p hp
  apply AnalyticAt.sub
  · exact analyticAt_const
  · apply AnalyticAt.cpow analyticAt_const analyticAt_id.neg
    exact Complex.natCast_mem_slitPlane.mpr
      (Nat.prime_of_mem_primeFactors hp).ne_zero

theorem principalDirichletEulerProduct_ne_zero_of_re_pos
    {N : ℕ} {s : ℂ} (hs : 0 < s.re) :
    principalDirichletEulerProduct N s ≠ 0 := by
  unfold principalDirichletEulerProduct
  rw [Finset.prod_ne_zero_iff]
  intro p hp
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpcastpos : 0 < (p : ℝ) := by exact_mod_cast hpprime.pos
  have hpow : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    change ‖((p : ℝ) : ℂ) ^ (-(s : ℂ))‖ < 1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpcastpos, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast hpprime.one_lt) (by linarith)
  intro hzero
  have hone : (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp hzero).symm
  have hnorm := congrArg norm hone
  rw [norm_one] at hnorm
  linarith

theorem analyticAt_principalDirichletInv_of_ofReal_pos
    (N : ℕ) {u : ℝ} (hu : 0 < u) :
    AnalyticAt ℂ (principalDirichletInv N) (u : ℂ) := by
  exact (analyticAt_invZeta_of_residueUnit_ne_zero
      (zetaResidueUnit_ne_zero_of_ofReal_pos hu)).mul
    ((principalDirichletEulerProduct_analyticAt N (u : ℂ)).inv
      (principalDirichletEulerProduct_ne_zero_of_re_pos (by simpa using hu)))

def principalDirichletEulerProductReal (N : ℕ) (u : ℝ) : ℝ :=
  ∏ p ∈ N.primeFactors, (1 - (p : ℝ) ^ (-u))

theorem principalDirichletEulerProduct_ofReal (N : ℕ) (u : ℝ) :
    principalDirichletEulerProduct N (u : ℂ) =
      ((principalDirichletEulerProductReal N u : ℝ) : ℂ) := by
  unfold principalDirichletEulerProduct principalDirichletEulerProductReal
  push_cast
  apply Finset.prod_congr rfl
  intro p hp
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg _
  have hcast : (-((u : ℝ) : ℂ)) = (((-u : ℝ)) : ℂ) := by push_cast; ring
  have hpc : (p : ℂ) = (((p : ℝ)) : ℂ) := by push_cast; ring
  rw [hpc, hcast, ← Complex.ofReal_cpow hp0]

theorem principalDirichletEulerProductReal_pos
    (N : ℕ) {u : ℝ} (hu : 0 < u) :
    0 < principalDirichletEulerProductReal N u := by
  unfold principalDirichletEulerProductReal
  apply Finset.prod_pos
  intro p hp
  apply sub_pos.mpr
  exact Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt) (by linarith)

def dirichletCharacterPositiveTerm
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (s : ℂ) (k : ℕ+) : ℂ :=
  chi ((k : ℕ) : ZMod N) * positiveDirichletTerm s k

theorem summable_dirichletCharacterPositiveTerm
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (dirichletCharacterPositiveTerm chi s) := by
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun k => norm_nonneg _)
    (fun k => by
      rw [dirichletCharacterPositiveTerm, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (norm_dirichletCharacter_le_one chi _))
    (summable_positiveDirichletTerm hs).norm

theorem tsum_dirichletCharacterPositiveTerm_eq_LFunction
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (s : ℂ) (hs : 1 < s.re) :
    (∑' k : ℕ+, dirichletCharacterPositiveTerm chi s k) =
      DirichletCharacter.LFunction chi s := by
  rw [DirichletCharacter.LFunction_eq_LSeries chi hs, LSeries]
  have hsum : Summable (fun k : ℕ => LSeries.term (fun x => chi (x : ZMod N)) s k) :=
    ZMod.LSeriesSummable_of_one_lt_re (fun x => chi x) hs
  calc
    (∑' k : ℕ+, dirichletCharacterPositiveTerm chi s k) =
        ∑' k : ℕ+, LSeries.term (fun x => chi (x : ZMod N)) s (k : ℕ) := by
      apply tsum_congr
      intro k
      rw [dirichletCharacterPositiveTerm,
        LSeries.term_of_ne_zero k.ne_zero]
      unfold positiveDirichletTerm
      rw [Complex.cpow_neg]
      rfl
    _ = ∑' k : ℕ, LSeries.term (fun x => chi (x : ZMod N)) s (k + 1) :=
      tsum_pnat_eq_tsum_succ
    _ = ∑' k : ℕ, LSeries.term (fun x => chi (x : ZMod N)) s k := by
      simpa [LSeries.term_zero] using hsum.sum_add_tsum_nat_add 1

theorem dirichletCharacterPositiveTerm_mul
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (s : ℂ) (a d : ℕ+) :
    dirichletCharacterPositiveTerm chi s (a * d) =
      dirichletCharacterPositiveTerm chi s a *
        dirichletCharacterPositiveTerm chi s d := by
  have hcastZ : ((((a * d : ℕ+) : ℕ) : ZMod N)) =
      (((a : ℕ) : ZMod N)) * (((d : ℕ) : ZMod N)) := by
    push_cast
    rfl
  have hcastC : ((((a * d : ℕ+) : ℕ) : ℂ)) =
      (((a : ℕ) : ℂ)) * (((d : ℕ) : ℂ)) := by
    push_cast
    rfl
  have ha : (0 : ℝ) ≤ (a : ℝ) := by positivity
  have hd : (0 : ℝ) ≤ (d : ℝ) := by positivity
  have hpow :
      ((((a : ℕ) : ℂ)) * (((d : ℕ) : ℂ))) ^ (-s) =
        (((a : ℕ) : ℂ)) ^ (-s) * (((d : ℕ) : ℂ)) ^ (-s) := by
    simpa using Complex.mul_cpow_ofReal_nonneg ha hd (-s)
  unfold dirichletCharacterPositiveTerm positiveDirichletTerm
  rw [hcastZ, map_mul, hcastC, hpow]
  ring

theorem dirichletCharacterPositiveTerm_mul_inv_add
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (s t : ℂ) (d : ℕ+) :
    dirichletCharacterPositiveTerm chi s d *
        dirichletCharacterPositiveTerm chi⁻¹ t d =
      dirichletCharacterPositiveTerm (1 : DirichletCharacter ℂ N) (s + t) d := by
  have hdne : (((d : ℕ) : ℂ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr d.ne_zero
  have hchar :
      chi (((d : ℕ) : ZMod N)) * chi⁻¹ (((d : ℕ) : ZMod N)) =
        (1 : DirichletCharacter ℂ N) (((d : ℕ) : ZMod N)) := by
    rw [← MulChar.mul_apply]
    simp
  have hpow : (((d : ℕ) : ℂ) ^ (-s)) * (((d : ℕ) : ℂ) ^ (-t)) =
      ((d : ℕ) : ℂ) ^ (-(s + t)) := by
    rw [← Complex.cpow_add _ _ hdne]
    congr 1
    ring
  unfold dirichletCharacterPositiveTerm positiveDirichletTerm
  calc
    chi ↑(d : ℕ) * ↑(d : ℕ) ^ (-s) *
          (chi⁻¹ ↑(d : ℕ) * ↑(d : ℕ) ^ (-t)) =
        (chi ↑(d : ℕ) * chi⁻¹ ↑(d : ℕ)) *
          (↑(d : ℕ) ^ (-s) * ↑(d : ℕ) ^ (-t)) := by ring
    _ = (1 : DirichletCharacter ℂ N) ↑(d : ℕ) *
        ↑(d : ℕ) ^ (-(s + t)) := by rw [hchar, hpow]

def visibleCoprimeCharacterMellinTerm
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (s t : ℂ) (q : ThetaCuspPrimitiveDirection) : ℂ :=
  dirichletCharacterPositiveTerm chi s q.1.1 *
    dirichletCharacterPositiveTerm chi⁻¹ t q.1.2

def visibleCoprimeCharacterMellinSymbol
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (s t : ℂ) : ℂ :=
  ∑' q : ThetaCuspPrimitiveDirection,
    visibleCoprimeCharacterMellinTerm chi s t q

theorem visibleCoprimeCharacterMellinTerm_eq_conj
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (s t : ℂ) (q : ThetaCuspPrimitiveDirection) :
    visibleCoprimeCharacterMellinTerm chi s t q =
      (chi ((q.1.1 : ℕ) : ZMod N) * positiveDirichletTerm s q.1.1) *
        ((starRingEnd ℂ) (chi ((q.1.2 : ℕ) : ZMod N)) *
          positiveDirichletTerm t q.1.2) := by
  unfold visibleCoprimeCharacterMellinTerm dirichletCharacterPositiveTerm
  rw [conj_dirichletCharacter_apply]

private theorem summable_dirichletCharacterPositivePair
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (s t : ℂ) (hs : 1 < s.re) (ht : 1 < t.re) :
    Summable (fun p : ℕ+ × ℕ+ =>
      dirichletCharacterPositiveTerm chi s p.1 *
        dirichletCharacterPositiveTerm chi⁻¹ t p.2) := by
  have hss := summable_dirichletCharacterPositiveTerm chi hs
  have htt := summable_dirichletCharacterPositiveTerm chi⁻¹ ht
  apply Summable.of_norm
  simpa only [norm_mul] using
    hss.norm.mul_of_nonneg htt.norm (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)

theorem summable_visibleCoprimeCharacterMellinTerm
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (s t : ℂ) (hs : 1 < s.re) (ht : 1 < t.re) :
    Summable (visibleCoprimeCharacterMellinTerm chi s t) := by
  exact (summable_dirichletCharacterPositivePair chi s t hs ht).comp_injective
    Subtype.val_injective

private theorem visibleCoprimeCharacterMellin_ray_factor
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (s t : ℂ) (q : ThetaCuspPrimitiveDirection) (d : ℕ+) :
    visibleCoprimeCharacterMellinTerm chi s t q *
        dirichletCharacterPositiveTerm (1 : DirichletCharacter ℂ N) (s + t) d =
      dirichletCharacterPositiveTerm chi s (q.1.1 * d) *
        dirichletCharacterPositiveTerm chi⁻¹ t (q.1.2 * d) := by
  rw [dirichletCharacterPositiveTerm_mul,
    dirichletCharacterPositiveTerm_mul]
  unfold visibleCoprimeCharacterMellinTerm
  have hd := dirichletCharacterPositiveTerm_mul_inv_add chi s t d
  rw [← hd]
  ring

theorem visibleCoprimeCharacterMellinSymbol_mul_principalLFunction
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (s t : ℂ) (hs : 1 < s.re) (ht : 1 < t.re) :
    visibleCoprimeCharacterMellinSymbol chi s t *
        DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N) (s + t) =
      DirichletCharacter.LFunction chi s *
        DirichletCharacter.LFunction chi⁻¹ t := by
  let f : ℕ+ × ℕ+ → ℂ := fun p =>
    dirichletCharacterPositiveTerm chi s p.1 *
      dirichletCharacterPositiveTerm chi⁻¹ t p.2
  have hfull : Summable f :=
    summable_dirichletCharacterPositivePair chi s t hs ht
  have hray : Summable (fun q : ThetaCuspPrimitiveRayIndex =>
      f (thetaCuspPrimitiveRayIndexToPositivePair q)) :=
    (Equiv.summable_iff thetaCuspPrimitiveRayIndexEquivPositivePair).2 hfull
  have hst : 1 < (s + t).re := by
    simp only [add_re]
    linarith
  have hdir := summable_visibleCoprimeCharacterMellinTerm chi s t hs ht
  have hd := summable_dirichletCharacterPositiveTerm
    (1 : DirichletCharacter ℂ N) hst
  have hprod : Summable (fun q : ThetaCuspPrimitiveRayIndex =>
      visibleCoprimeCharacterMellinTerm chi s t q.1 *
        dirichletCharacterPositiveTerm (1 : DirichletCharacter ℂ N) (s + t) q.2) := by
    apply hray.congr
    rintro ⟨q, d⟩
    exact (visibleCoprimeCharacterMellin_ray_factor chi s t q d).symm
  calc
    visibleCoprimeCharacterMellinSymbol chi s t *
        DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N) (s + t) =
        (∑' q : ThetaCuspPrimitiveDirection,
          visibleCoprimeCharacterMellinTerm chi s t q) *
          (∑' d : ℕ+, dirichletCharacterPositiveTerm
            (1 : DirichletCharacter ℂ N) (s + t) d) := by
      rw [visibleCoprimeCharacterMellinSymbol,
        tsum_dirichletCharacterPositiveTerm_eq_LFunction
          (1 : DirichletCharacter ℂ N) (s + t) hst]
    _ = ∑' q : ThetaCuspPrimitiveRayIndex,
          visibleCoprimeCharacterMellinTerm chi s t q.1 *
            dirichletCharacterPositiveTerm
              (1 : DirichletCharacter ℂ N) (s + t) q.2 :=
      hdir.tsum_mul_tsum hd hprod
    _ = ∑' q : ThetaCuspPrimitiveRayIndex,
          f (thetaCuspPrimitiveRayIndexToPositivePair q) := by
      apply tsum_congr
      rintro ⟨q, d⟩
      exact visibleCoprimeCharacterMellin_ray_factor chi s t q d
    _ = ∑' p : ℕ+ × ℕ+, f p :=
      (tsum_thetaCuspPositivePair_eq_primitiveRay f).symm
    _ = (∑' a : ℕ+, dirichletCharacterPositiveTerm chi s a) *
          (∑' b : ℕ+, dirichletCharacterPositiveTerm chi⁻¹ t b) := by
      exact (summable_dirichletCharacterPositiveTerm chi hs).tsum_mul_tsum
        (summable_dirichletCharacterPositiveTerm chi⁻¹ ht) hfull |>.symm
    _ = DirichletCharacter.LFunction chi s *
          DirichletCharacter.LFunction chi⁻¹ t := by
      rw [tsum_dirichletCharacterPositiveTerm_eq_LFunction chi s hs,
        tsum_dirichletCharacterPositiveTerm_eq_LFunction chi⁻¹ t ht]

theorem visibleCoprimeCharacterMellinSymbol_eq_LFunction_quotient
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (s t : ℂ) (hs : 1 < s.re) (ht : 1 < t.re) :
    visibleCoprimeCharacterMellinSymbol chi s t =
      DirichletCharacter.LFunction chi s *
        DirichletCharacter.LFunction chi⁻¹ t /
          DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N) (s + t) := by
  have hst : 1 ≤ (s + t).re := by
    simp only [add_re]
    linarith
  have hne1 : s + t ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [add_re, one_re] at hre
    linarith
  have hnz := DirichletCharacter.LFunction_ne_zero_of_one_le_re
    (1 : DirichletCharacter ℂ N) (Or.inr hne1) hst
  apply mul_right_cancel₀ hnz
  rw [visibleCoprimeCharacterMellinSymbol_mul_principalLFunction chi s t hs ht]
  field_simp

private theorem conj_ofReal_cpow_pos {u : ℝ} (hu : 0 < u) (z : ℂ) :
    (starRingEnd ℂ) ((u : ℂ) ^ z) =
      (u : ℂ) ^ ((starRingEnd ℂ) z) := by
  have harg : ((u : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hu.le]
    exact ne_of_lt Real.pi_pos
  have h := Complex.conj_cpow (u : ℂ) ((starRingEnd ℂ) z) harg
  rw [Complex.conj_ofReal, RingHomInvPair.comp_apply_eq] at h
  exact h.symm

theorem LFunction_inv_conj_of_one_lt_re
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (s : ℂ) (hs : 1 < s.re) :
    DirichletCharacter.LFunction chi⁻¹ ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (DirichletCharacter.LFunction chi s) := by
  have hsc : 1 < ((starRingEnd ℂ) s).re := by simpa using hs
  rw [← tsum_dirichletCharacterPositiveTerm_eq_LFunction chi⁻¹ _ hsc,
    ← tsum_dirichletCharacterPositiveTerm_eq_LFunction chi _ hs,
    Complex.conj_tsum]
  apply tsum_congr
  intro k
  have hk : 0 < ((k : ℕ) : ℝ) := by exact_mod_cast k.pos
  have hpow :
      (starRingEnd ℂ) ((((k : ℕ) : ℂ)) ^ (-s)) =
        (((k : ℕ) : ℂ)) ^ (-((starRingEnd ℂ) s)) := by
    simpa using (conj_ofReal_cpow_pos hk (-s))
  unfold dirichletCharacterPositiveTerm positiveDirichletTerm
  rw [map_mul, conj_dirichletCharacter_apply, hpow]

theorem LFunction_inv_conj
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (hchi : chi ≠ 1) (s : ℂ) :
    DirichletCharacter.LFunction chi⁻¹ ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (DirichletCharacter.LFunction chi s) := by
  have hinv : chi⁻¹ ≠ 1 := inv_ne_one.mpr hchi
  let F : ℂ → ℂ := fun z =>
    DirichletCharacter.LFunction chi⁻¹ z -
      (starRingEnd ℂ)
        (DirichletCharacter.LFunction chi ((starRingEnd ℂ) z))
  have hF : AnalyticOnNhd ℂ F Set.univ := by
    intro z hz
    exact ((DirichletCharacter.differentiable_LFunction hinv).analyticAt z).sub
      (((DirichletCharacter.differentiable_LFunction hchi).analyticAt
        ((starRingEnd ℂ) z)).conj_comp_conj)
  have hopen : IsOpen {z : ℂ | 1 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hmem : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by norm_num
  have heventMem : ∀ᶠ z : ℂ in nhds (2 : ℂ), z ∈ {z : ℂ | 1 < z.re} :=
    hopen.mem_nhds hmem
  have hevent : F =ᶠ[nhds (2 : ℂ)] 0 := heventMem.mono (fun z hz => by
    dsimp [F]
    rw [sub_eq_zero]
    simpa using LFunction_inv_conj_of_one_lt_re chi
      ((starRingEnd ℂ) z) (by simpa using hz))
  have hzero : Set.EqOn F 0 (Set.univ : Set ℂ) :=
    hF.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ (2 : ℂ)) hevent
  have hs := hzero (Set.mem_univ ((starRingEnd ℂ) s))
  dsimp [F] at hs
  simpa using sub_eq_zero.mp hs

/-- An actual zero in the open critical strip of a fixed primitive,
nonprincipal Dirichlet character. -/
structure PrimitiveDirichletLZero
    (n : ℕ) (chi : PrimitiveNonprincipalDirichletCharacter n) where
  point : ℂ
  re_pos : 0 < point.re
  re_lt_one : point.re < 1
  vanishes : DirichletCharacter.LFunction chi.1.1 point = 0

/-- Analytic multiplicity of an actual primitive Dirichlet `L`-zero. -/
def primitiveDirichletLZeroMultiplicity
    {n : ℕ} {chi : PrimitiveNonprincipalDirichletCharacter n}
    (rho : PrimitiveDirichletLZero n chi) : ℕ :=
  (analyticOrderAt (DirichletCharacter.LFunction chi.1.1) rho.point).toNat

theorem analyticOrderAt_LFunction_ne_top_at_primitiveDirichletLZero
    {n : ℕ} {chi : PrimitiveNonprincipalDirichletCharacter n}
    (rho : PrimitiveDirichletLZero n chi) :
    analyticOrderAt (DirichletCharacter.LFunction chi.1.1) rho.point ≠ ⊤ := by
  apply analyticOrderAt_ne_top_of_entire_exists_ne_zero
  · intro z hz
    exact (DirichletCharacter.differentiable_LFunction chi.1.2).analyticAt z
  · refine ⟨(2 : ℂ), ?_⟩
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re chi.1.1
      (Or.inl chi.1.2) (by norm_num)

/-- All lower jets vanish and the jet at the exact analytic multiplicity is nonzero. -/
theorem primitiveDirichletLZero_exactJets
    {n : ℕ} {chi : PrimitiveNonprincipalDirichletCharacter n}
    (rho : PrimitiveDirichletLZero n chi) :
    (∀ j < primitiveDirichletLZeroMultiplicity rho,
      iteratedDeriv j (DirichletCharacter.LFunction chi.1.1) rho.point = 0) ∧
    iteratedDeriv (primitiveDirichletLZeroMultiplicity rho)
      (DirichletCharacter.LFunction chi.1.1) rho.point ≠ 0 := by
  have hana : AnalyticAt ℂ (DirichletCharacter.LFunction chi.1.1) rho.point :=
    (DirichletCharacter.differentiable_LFunction chi.1.2).analyticAt rho.point
  have hm :
      ((primitiveDirichletLZeroMultiplicity rho : ℕ) : ℕ∞) =
        analyticOrderAt (DirichletCharacter.LFunction chi.1.1) rho.point :=
    ENat.coe_toNat
      (analyticOrderAt_LFunction_ne_top_at_primitiveDirichletLZero rho)
  have hjets :=
    GaloisForLFunctions.RHTower.GelfondSchneiderProof.analyticOrderAt_eq_nat_imp_iteratedDeriv_eq_zero
      hana (primitiveDirichletLZeroMultiplicity rho) hm.symm
  simpa only [iteratedDeriv_eq_iterate] using hjets

/-- Every Dirichlet `L`-jet is transported to the inverse character by
Schwarz reflection. -/
theorem iteratedDeriv_LFunction_inv_conj
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (hchi : chi ≠ 1) (m : ℕ) (z : ℂ) :
    iteratedDeriv m (DirichletCharacter.LFunction chi⁻¹)
        ((starRingEnd ℂ) z) =
      (starRingEnd ℂ)
        (iteratedDeriv m (DirichletCharacter.LFunction chi) z) := by
  have hfun :
      (starRingEnd ℂ) ∘ DirichletCharacter.LFunction chi ∘
          (starRingEnd ℂ) =
        DirichletCharacter.LFunction chi⁻¹ := by
    funext w
    simpa [Function.comp_def] using
      (LFunction_inv_conj chi hchi ((starRingEnd ℂ) w)).symm
  have h := congrFun
    (iteratedDeriv_conj_conj (DirichletCharacter.LFunction chi) m)
      ((starRingEnd ℂ) z)
  rw [hfun] at h
  simpa [Function.comp_def] using h

/-- Holomorphic continuation of the primitive-character visible-coprime symbol. -/
def visibleCoprimeDirichletKernel
    (n : ℕ) (chi : PrimitiveNonprincipalDirichletCharacter n)
    (s t : ℂ) : ℂ :=
  DirichletCharacter.LFunction chi.1.1 s *
    DirichletCharacter.LFunction chi.1.1⁻¹ t *
      principalDirichletInv (n + 1) (s + t)

/-- Hermitian mixed jet at an actual primitive Dirichlet `L`-zero. -/
def visibleCoprimeDirichletMixedJet
    {n : ℕ} {chi : PrimitiveNonprincipalDirichletCharacter n}
    (rho : PrimitiveDirichletLZero n chi) : ℂ :=
  let m := primitiveDirichletLZeroMultiplicity rho
  iteratedDeriv m
    (fun s => iteratedDeriv m
      (fun t => visibleCoprimeDirichletKernel n chi s t)
        ((starRingEnd ℂ) rho.point)) rho.point

/-- The two Leibniz expansions leave only the leading conjugate pair of
Dirichlet `L`-jets. -/
theorem visibleCoprimeDirichletMixedJet_eq_raw
    {n : ℕ} {chi : PrimitiveNonprincipalDirichletCharacter n}
    (rho : PrimitiveDirichletLZero n chi) :
    visibleCoprimeDirichletMixedJet rho =
      iteratedDeriv (primitiveDirichletLZeroMultiplicity rho)
          (DirichletCharacter.LFunction chi.1.1) rho.point *
        iteratedDeriv (primitiveDirichletLZeroMultiplicity rho)
          (DirichletCharacter.LFunction chi.1.1⁻¹)
            ((starRingEnd ℂ) rho.point) *
        principalDirichletInv (n + 1)
          (rho.point + (starRingEnd ℂ) rho.point) := by
  have hinv : chi.1.1⁻¹ ≠ 1 := inv_ne_one.mpr chi.1.2
  have hsum :
      rho.point + (starRingEnd ℂ) rho.point =
        ((2 * rho.point.re : ℝ) : ℂ) :=
    add_conj_eq_ofReal_two_re rho.point
  have hpos : 0 < 2 * rho.point.re := by linarith [rho.re_pos]
  have hf : ContDiffAt ℂ (primitiveDirichletLZeroMultiplicity rho)
      (DirichletCharacter.LFunction chi.1.1) rho.point :=
    ((DirichletCharacter.differentiable_LFunction chi.1.2).analyticAt
      rho.point).contDiffAt
  have hg : ContDiffAt ℂ (primitiveDirichletLZeroMultiplicity rho)
      (DirichletCharacter.LFunction chi.1.1⁻¹)
        ((starRingEnd ℂ) rho.point) :=
    ((DirichletCharacter.differentiable_LFunction hinv).analyticAt
      ((starRingEnd ℂ) rho.point)).contDiffAt
  have hh : ContDiffAt ℂ (primitiveDirichletLZeroMultiplicity rho)
      (principalDirichletInv (n + 1))
        (rho.point + (starRingEnd ℂ) rho.point) := by
    rw [hsum]
    exact (analyticAt_principalDirichletInv_of_ofReal_pos (n + 1) hpos).contDiffAt
  have hfzero : ∀ j < primitiveDirichletLZeroMultiplicity rho,
      iteratedDeriv j (DirichletCharacter.LFunction chi.1.1) rho.point = 0 :=
    (primitiveDirichletLZero_exactJets rho).1
  have hgzero : ∀ j < primitiveDirichletLZeroMultiplicity rho,
      iteratedDeriv j (DirichletCharacter.LFunction chi.1.1⁻¹)
        ((starRingEnd ℂ) rho.point) = 0 := by
    intro j hj
    rw [iteratedDeriv_LFunction_inv_conj chi.1.1 chi.1.2]
    simp [hfzero j hj]
  unfold visibleCoprimeDirichletMixedJet visibleCoprimeDirichletKernel
  exact complex_mixedAddProductJet_of_vanishing_below
    (primitiveDirichletLZeroMultiplicity rho) hf hg hh hfzero hgzero

/-- Exact primitive-character zero-jet formula `(V11)`, with the principal
denominator reciprocal filled holomorphically at `s+t=1`. -/
theorem visibleCoprimeDirichletMixedJet_eq
    {n : ℕ} {chi : PrimitiveNonprincipalDirichletCharacter n}
    (rho : PrimitiveDirichletLZero n chi) :
    visibleCoprimeDirichletMixedJet rho =
      ((Complex.normSq
        (iteratedDeriv (primitiveDirichletLZeroMultiplicity rho)
          (DirichletCharacter.LFunction chi.1.1) rho.point) : ℝ) : ℂ) *
        principalDirichletInv (n + 1)
          (((2 * rho.point.re : ℝ) : ℂ)) := by
  rw [visibleCoprimeDirichletMixedJet_eq_raw,
    iteratedDeriv_LFunction_inv_conj chi.1.1 chi.1.2,
    add_conj_eq_ofReal_two_re, Complex.mul_conj]

/-- The regular reciprocal of the principal Dirichlet `L`-function is
negative left of its pole. -/
theorem re_principalDirichletInv_two_mul_neg
    (N : ℕ) {sigma : ℝ} (h0 : 0 < sigma) (hhalf : sigma < 1 / 2) :
    (principalDirichletInv N (((2 * sigma : ℝ) : ℂ))).re < 0 := by
  rw [principalDirichletInv, principalDirichletEulerProduct_ofReal,
    ← Complex.ofReal_inv]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  exact mul_neg_of_neg_of_pos
    (re_invZeta_two_mul_neg h0 hhalf)
    (inv_pos.mpr
      (principalDirichletEulerProductReal_pos N (by linarith)))

/-- The regular reciprocal of the principal Dirichlet `L`-function is
positive right of its pole. -/
theorem re_principalDirichletInv_two_mul_pos
    (N : ℕ) {sigma : ℝ} (hhalf : 1 / 2 < sigma) :
    0 < (principalDirichletInv N (((2 * sigma : ℝ) : ℂ))).re := by
  rw [principalDirichletInv, principalDirichletEulerProduct_ofReal,
    ← Complex.ofReal_inv]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  exact mul_pos
    (re_invZeta_two_mul_pos hhalf)
    (inv_pos.mpr
      (principalDirichletEulerProductReal_pos N (by linarith)))

/-- The pole-filled reciprocal of every principal Dirichlet `L`-function
vanishes at `1`. -/
theorem principalDirichletInv_one (N : ℕ) :
    principalDirichletInv N 1 = 0 := by
  simp [principalDirichletInv, Sieve.invZeta_one]

/-- On every positive doubled abscissa the principal reciprocal is real. -/
theorem principalDirichletInv_two_mul_im_eq_zero
    (N : ℕ) {sigma : ℝ} (h0 : 0 < sigma) :
    (principalDirichletInv N (((2 * sigma : ℝ) : ℂ))).im = 0 := by
  rcases lt_trichotomy sigma (1 / 2) with hlt | heq | hgt
  · obtain ⟨z, hz, hzeta⟩ := riemannZeta_two_mul_neg h0 hlt
    have hne : (((2 * sigma : ℝ) : ℂ)) ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      norm_num at hre
      linarith
    rw [principalDirichletInv, Sieve.invZeta_eq_inv hne, hzeta,
      principalDirichletEulerProduct_ofReal,
      ← Complex.ofReal_inv, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
    simp
  · rw [heq]
    norm_num [principalDirichletInv_one]
  · have hne : (((2 * sigma : ℝ) : ℂ)) ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      norm_num at hre
      linarith
    rw [principalDirichletInv, Sieve.invZeta_eq_inv hne,
      riemannZeta_two_mul_eq_ofReal hgt,
      principalDirichletEulerProduct_ofReal,
      ← Complex.ofReal_inv, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
    simp

/-- The primitive-character Hermitian mixed jet is real. -/
theorem visibleCoprimeDirichletMixedJet_im_eq_zero
    {n : ℕ} {chi : PrimitiveNonprincipalDirichletCharacter n}
    (rho : PrimitiveDirichletLZero n chi) :
    (visibleCoprimeDirichletMixedJet rho).im = 0 := by
  rw [visibleCoprimeDirichletMixedJet_eq]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul]
  rw [principalDirichletInv_two_mul_im_eq_zero (n + 1) rho.re_pos, mul_zero]
  norm_num

/-- Left of the critical line the primitive-character visible-coprime zero
jet is strictly negative. -/
theorem visibleCoprimeDirichletMixedJet_re_neg_of_re_lt_half
    {n : ℕ} {chi : PrimitiveNonprincipalDirichletCharacter n}
    (rho : PrimitiveDirichletLZero n chi) (hhalf : rho.point.re < 1 / 2) :
    (visibleCoprimeDirichletMixedJet rho).re < 0 := by
  rw [visibleCoprimeDirichletMixedJet_eq]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  exact mul_neg_of_pos_of_neg
    ((Complex.normSq_pos).2 (primitiveDirichletLZero_exactJets rho).2)
    (re_principalDirichletInv_two_mul_neg (n + 1) rho.re_pos hhalf)

/-- Right of the critical line the primitive-character visible-coprime zero
jet is strictly positive. -/
theorem visibleCoprimeDirichletMixedJet_re_pos_of_half_lt_re
    {n : ℕ} {chi : PrimitiveNonprincipalDirichletCharacter n}
    (rho : PrimitiveDirichletLZero n chi) (hhalf : 1 / 2 < rho.point.re) :
    0 < (visibleCoprimeDirichletMixedJet rho).re := by
  rw [visibleCoprimeDirichletMixedJet_eq]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  exact mul_pos
    ((Complex.normSq_pos).2 (primitiveDirichletLZero_exactJets rho).2)
    (re_principalDirichletInv_two_mul_pos (n + 1) hhalf)

/-- Exact critical-line vanishing certificate in the primitive-character
form of `(V9)`. -/
theorem visibleCoprimeDirichletMixedJet_eq_zero_iff
    {n : ℕ} {chi : PrimitiveNonprincipalDirichletCharacter n}
    (rho : PrimitiveDirichletLZero n chi) :
    visibleCoprimeDirichletMixedJet rho = 0 ↔ rho.point.re = 1 / 2 := by
  constructor
  · intro hzero
    rcases lt_trichotomy rho.point.re (1 / 2) with hlt | heq | hgt
    · have hneg := visibleCoprimeDirichletMixedJet_re_neg_of_re_lt_half rho hlt
      rw [hzero] at hneg
      norm_num at hneg
    · exact heq
    · have hpos := visibleCoprimeDirichletMixedJet_re_pos_of_half_lt_re rho hgt
      rw [hzero] at hpos
      norm_num at hpos
  · intro hhalf
    rw [visibleCoprimeDirichletMixedJet_eq, hhalf]
    norm_num [principalDirichletInv_one]

/-- Negative chamber equivalence for primitive Dirichlet zero jets. -/
theorem visibleCoprimeDirichletMixedJet_re_neg_iff
    {n : ℕ} {chi : PrimitiveNonprincipalDirichletCharacter n}
    (rho : PrimitiveDirichletLZero n chi) :
    (visibleCoprimeDirichletMixedJet rho).re < 0 ↔ rho.point.re < 1 / 2 := by
  constructor
  · intro hneg
    rcases lt_trichotomy rho.point.re (1 / 2) with hlt | heq | hgt
    · exact hlt
    · have hzero := (visibleCoprimeDirichletMixedJet_eq_zero_iff rho).2 heq
      rw [hzero] at hneg
      norm_num at hneg
    · have hpos := visibleCoprimeDirichletMixedJet_re_pos_of_half_lt_re rho hgt
      linarith
  · exact visibleCoprimeDirichletMixedJet_re_neg_of_re_lt_half rho

/-- Positive chamber equivalence for primitive Dirichlet zero jets. -/
theorem visibleCoprimeDirichletMixedJet_re_pos_iff
    {n : ℕ} {chi : PrimitiveNonprincipalDirichletCharacter n}
    (rho : PrimitiveDirichletLZero n chi) :
    0 < (visibleCoprimeDirichletMixedJet rho).re ↔ 1 / 2 < rho.point.re := by
  constructor
  · intro hpos
    rcases lt_trichotomy rho.point.re (1 / 2) with hlt | heq | hgt
    · have hneg := visibleCoprimeDirichletMixedJet_re_neg_of_re_lt_half rho hlt
      linarith
    · have hzero := (visibleCoprimeDirichletMixedJet_eq_zero_iff rho).2 heq
      rw [hzero] at hpos
      norm_num at hpos
    · exact hgt
  · exact visibleCoprimeDirichletMixedJet_re_pos_of_half_lt_re rho

end

end RHTower
