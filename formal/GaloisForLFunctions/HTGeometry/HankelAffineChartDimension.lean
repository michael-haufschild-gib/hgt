import GaloisForLFunctions.HTGeometry.HankelSliceBirational
import GaloisForLFunctions.HTGeometry.ReciprocalSourceGeometry
import GaloisForLFunctions.HTGeometry.HankelSingularLocus
import GaloisForLFunctions.HTGeometry.AffineDomainRationalPointCut

/-!
# The affine chart `x_0 = 1` of the Hankel secant variety has dimension `2r − 1`

For `0 < r`, `r ≤ j`, `j + r ≤ N`, the chart ring
`ChartRing K r N j = K[x_0, …, x_{N−1}] ⧸ (secantIdealUpTo K N r j + (x_0 − 1))` has Krull dimension
`2r − 1 + (N − j − r)` (`ringKrullDim_chartRing`). For `j = N − r` this is the affine chart of the
secant variety, of dimension `2r − 1` (`ringKrullDim_hankelAffineChart`).

**Proof.** The secant ring `B = K[x]/secantIdealUpTo` of the first `j + r` moments has dimension
`2r + (N − j − r)`: it is `HankelSecantRing K (j+r) r` with `N − j − r` free variables
(`ringKrullDim_extend`, `ringKrullDim_hankelSecantRing`). It is a domain (`secantRing_isDomain`)
and `x_0 − 1` is nonzero in it, since every minor vanishes at the origin. Cutting by a nonzero
element lowers the dimension by at least one (`ringKrullDim_quotient_succ_le_of_nonZeroDivisor`).
Since `x_0 − 1` vanishes at the rational point `e_0 = (1, 0, …, 0)` of the variety (every minor
has a zero column there), it lowers the dimension by at most one
(`ringKrullDim_le_quotient_add_one_of_rationalPoint`).
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

/-- A Hankel minor of size `r + 1 ≥ 2` vanishes at every point supported on the first coordinate. -/
theorem eval_finiteHankelMaximalMinorOver_eq_zero {K : Type} [Field K] {N r : ℕ} (hr : 0 < r)
    (c : Fin (r + 1) → ℕ) (hbound : ∀ i, r + 1 + c i ≤ N) (hc : StrictMono c) (x : Fin N → K)
    (hx : ∀ i : Fin N, (i : ℕ) ≠ 0 → x i = 0) :
    eval x (RHTower.finiteHankelMaximalMinorOver K c hbound) = 0 := by
  rw [RHTower.finiteHankelMaximalMinorOver, RingHom.map_det]
  refine Matrix.det_eq_zero_of_column_eq_zero ⟨1, by omega⟩ fun i => ?_
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, eval_X]
  apply hx
  simp only [RHTower.finiteHankelIndex]
  have : c 0 < c ⟨1, by omega⟩ := hc (show (0 : Fin (r + 1)) < ⟨1, by omega⟩ from by
    rw [Fin.lt_def]; simp)
  omega

theorem secantIdealUpTo_le_ker_eval {K : Type} [Field K] {N r j : ℕ} (hr : 0 < r)
    (x : Fin N → K) (hx : ∀ i : Fin N, (i : ℕ) ≠ 0 → x i = 0) :
    _root_.HTGeometry.secantIdealUpTo K N r j ≤ RingHom.ker (eval x) := by
  rw [_root_.HTGeometry.secantIdealUpTo, Ideal.span_le]
  rintro p ⟨c, hbound, hc, -, rfl⟩
  exact eval_finiteHankelMaximalMinorOver_eq_zero hr c hbound hc x hx

/-- **The chart rings have dimension `2r − 1 + (N − j − r)`.** -/
theorem ringKrullDim_chartRing (K : Type) [Field K] [CharZero K] {N r j : ℕ} (hr : 0 < r)
    (hrj : r ≤ j) (hj : j + r ≤ N) :
    ringKrullDim (_root_.HTGeometry.ChartRing K r N j) =
      ((2 * r - 1 + (N - j - r) : ℕ) : WithBot ℕ∞) := by
  obtain ⟨f, rfl⟩ := Nat.exists_eq_add_of_le hj
  set I := _root_.HTGeometry.secantIdealUpTo K (j + r + f) r j with hI
  -- the secant ring has dimension `2r + f`
  have hIeq : I = (RHTower.finiteHankelSecantIdeal K (j + r) r).map (rename (Fin.castAdd f)) := by
    rw [_root_.HTGeometry.map_castAdd_secantIdeal (j + r) r f (by omega), Nat.add_sub_cancel]
  have hdimB : ringKrullDim (MvPolynomial (Fin (j + r + f)) K ⧸ I) =
      ((2 * r + f : ℕ) : WithBot ℕ∞) := by
    have hsec := ringKrullDim_hankelSecantRing K (N := j + r) (r := r) (by omega)
    rw [hIeq, _root_.HTGeometry.ringKrullDim_extend]
    erw [hsec]
    push_cast; rfl
  haveI : IsDomain (MvPolynomial (Fin (j + r + f)) K ⧸ I) :=
    _root_.HTGeometry.secantRing_isDomain (K := K) (r := r) (N := j + r + f) (j := j) (by omega)
  -- the chart is the quotient of the secant ring by `x_0 − 1`
  have hN : 0 < j + r + f := by omega
  set g : MvPolynomial (Fin (j + r + f)) K ⧸ I :=
    Ideal.Quotient.mk I (_root_.HTGeometry.firstMoment K (j + r + f) - 1) with hg
  set J : Ideal (MvPolynomial (Fin (j + r + f)) K) :=
    Ideal.span {_root_.HTGeometry.firstMoment K (j + r + f) - 1} with hJdef
  have hJ : J.map (Ideal.Quotient.mk I) = Ideal.span {g} := by
    rw [hJdef, Ideal.map_span, Set.image_singleton]
  have hchart : _root_.HTGeometry.ChartRing K r (j + r + f) j ≃+*
      (MvPolynomial (Fin (j + r + f)) K ⧸ I) ⧸ Ideal.span {g} :=
    ((DoubleQuot.quotQuotEquivQuotSup I J).symm).trans (Ideal.quotEquivOfEq hJ)
  have hdimC : ringKrullDim (_root_.HTGeometry.ChartRing K r (j + r + f) j) =
      ringKrullDim ((MvPolynomial (Fin (j + r + f)) K ⧸ I) ⧸ Ideal.span {g}) :=
    ringKrullDim_eq_of_ringEquiv (R := _root_.HTGeometry.ChartRing K r (j + r + f) j)
      (S := (MvPolynomial (Fin (j + r + f)) K ⧸ I) ⧸ Ideal.span {g}) hchart
  rw [hdimC]
  have hfm : _root_.HTGeometry.firstMoment K (j + r + f) = X ⟨0, hN⟩ := by
    rw [_root_.HTGeometry.firstMoment, dif_pos hN]
  -- `x_0 − 1` is nonzero
  have hg0 : g ≠ 0 := by
    intro h
    rw [hg, Ideal.Quotient.eq_zero_iff_mem] at h
    have h0 := secantIdealUpTo_le_ker_eval (K := K) (N := j + r + f) (j := j) hr 0
      (fun _ _ => rfl) h
    rw [RingHom.mem_ker, hfm, map_sub, eval_X, map_one] at h0
    simp at h0
  have hnzd : g ∈ nonZeroDivisors (MvPolynomial (Fin (j + r + f)) K ⧸ I) :=
    mem_nonZeroDivisors_of_ne_zero hg0
  have hupper := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hnzd
  -- the rational point `e_0`
  set e0 : Fin (j + r + f) → K := fun i => if (i : ℕ) = 0 then 1 else 0 with he0
  have he0z : ∀ i : Fin (j + r + f), (i : ℕ) ≠ 0 → e0 i = 0 := fun i hi => by
    simp [he0, hi]
  have hIle : I ≤ RingHom.ker (aeval e0 : MvPolynomial (Fin (j + r + f)) K →ₐ[K] K) := by
    intro p hp
    have := secantIdealUpTo_le_ker_eval (K := K) (N := j + r + f) (j := j) hr e0 he0z hp
    rw [RingHom.mem_ker] at this ⊢
    simpa [MvPolynomial.coe_aeval_eq_eval] using this
  set ε : (MvPolynomial (Fin (j + r + f)) K ⧸ I) →ₐ[K] K :=
    Ideal.Quotient.liftₐ I (aeval e0) (fun p hp => hIle hp) with hε
  have hεg : ε g = 0 := by
    simp [hε, hg, hfm, he0]
  have hlower := ringKrullDim_le_quotient_add_one_of_rationalPoint ε hg0 hεg
  -- conclude
  haveI : Nontrivial ((MvPolynomial (Fin (j + r + f)) K ⧸ I) ⧸ Ideal.span {g}) := by
    refine Ideal.Quotient.nontrivial_iff.mpr ?_
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    have := hu.map ε
    rw [hεg] at this
    exact not_isUnit_zero this
  obtain ⟨s, hs⟩ := exists_ringKrullDim_eq_of_finiteType K
    ((MvPolynomial (Fin (j + r + f)) K ⧸ I) ⧸ Ideal.span {g})
  rw [hs] at hupper hlower ⊢
  rw [hdimB] at hupper hlower
  have h2 : s + 1 = 2 * r + f := by
    have := le_antisymm hupper hlower
    have e : ((s : ℕ∞) : WithBot ℕ∞) + 1 = (((s + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      push_cast; rfl
    rw [e, WithBot.coe_natCast] at this
    have h' : ((s + 1 : ℕ) : ℕ∞) = ((2 * r + f : ℕ) : ℕ∞) := WithBot.coe_injective (by
      rw [WithBot.coe_natCast, WithBot.coe_natCast]; exact this)
    exact_mod_cast h'
  have h3 : s = 2 * r - 1 + (j + r + f - j - r) := by omega
  rw [h3]
  rfl

/-- **The affine chart `x_0 = 1` of the Hankel secant variety has dimension `2r − 1`.** -/
theorem ringKrullDim_hankelAffineChart (K : Type) [Field K] [CharZero K] {N r : ℕ} (hr : 0 < r)
    (hrN : 2 * r ≤ N) :
    ringKrullDim (MvPolynomial (Fin N) K ⧸ (RHTower.finiteHankelSecantIdeal K N r ⊔
      Ideal.span {_root_.HTGeometry.firstMoment K N - 1})) = ((2 * r - 1 : ℕ) : WithBot ℕ∞) := by
  have h := ringKrullDim_chartRing K (N := N) (r := r) (j := N - r) hr (by omega) (by omega)
  rw [show N - (N - r) - r = 0 by omega, add_zero] at h
  rw [← h, ← _root_.HTGeometry.secantIdealUpTo_self]
  rfl

end

end GaloisForLFunctions.HTGeometry
