import GaloisForLFunctions.HTGeometry.TripticMultiplicativeSourceClass
import GaloisForLFunctions.HTGeometry.TripticChargeClassFunction
import GaloisForLFunctions.HTGeometry.TripticCornerAccumulation
import GaloisForLFunctions.HTGeometry.TripticNormalForm

/-!
# The integral orbit divisor of a triptic source, as a finitely supported divisor on `ℂ/H₃`

The orbital charge of a member of the multiplicative triptic class is invariant under the period
group `H₃ = ℤ + ℤτ + ℤσ`: along `σ` by orbit reindexing, along `1` by exact periodicity, and along
`τ` because the mixed germ constraint makes the shift-quotient divisor `τ`-invariant.  It therefore
descends to the orbit space `ℂ ⧸ H₃`, where its support is finite: the shift-order support is
`1`- and `τ`-invariant, so every charged class has a representative with nonzero shift order inside
one compact fundamental parallelogram of the lattice `ℤ + ℤτ`, and the divisor of a meromorphic
function meets a compact set finitely.

* `shiftOrder_add_tau_of_source`, `finiteShiftSupport_of_source`;
* `tripticPeriodGroup`, `tripticChargeClass`, `tripticChargeClass_mk`;
* `finite_support_tripticChargeClass`, `tripticDivisor`, `tripticDivisor_mk`.
-/

open Filter Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {τ σ : ℂ} {Y : ℂ → ℂ} {Cst : ℂ}

/-! ### Shift-order invariance along `τ` from the germ constraint -/

/-- The residue coefficient of the logarithmic shift difference is `τ`-periodic: the mixed germ
constraint adds only a constant under a `τ`-step, and constants have no principal part. -/
theorem laurentCoeff_shiftDiff_logDeriv_add_tau
    (hY : TripticMultiplicativeSource τ σ Y Cst) (w : ℂ) {ℓ : ℤ} (hℓ : ℓ < 0) :
    laurentCoeff (fun z ↦ logDeriv Y (z + σ) - logDeriv Y z) (w + τ) ℓ
      = laurentCoeff (fun z ↦ logDeriv Y (z + σ) - logDeriv Y z) w ℓ := by
  have hFmero : MeromorphicOn (logDeriv Y) (Set.univ : Set ℂ) := fun z _ ↦
    ((hY.mero z (Set.mem_univ z)).deriv).div (hY.mero z (Set.mem_univ z))
  have hGmero : MeromorphicOn (fun z ↦ logDeriv Y (z + σ) - logDeriv Y z)
      (Set.univ : Set ℂ) := fun z _ ↦
    (meromorphicAt_comp_add.mpr (hFmero (z + σ) (Set.mem_univ _))).sub
      (hFmero z (Set.mem_univ z))
  have hshift : laurentCoeff (fun z ↦ logDeriv Y (z + σ) - logDeriv Y z) (w + τ) ℓ
      = laurentCoeff (fun z ↦ logDeriv Y (z + τ + σ) - logDeriv Y (z + τ)) w ℓ := by
    have hcomp := laurentCoeff_comp_add
      (fun z ↦ logDeriv Y (z + σ) - logDeriv Y z) w τ ℓ
    rw [← hcomp]
  have hev : (fun z ↦ logDeriv Y (z + τ + σ) - logDeriv Y (z + τ))
      =ᶠ[𝓝[≠] w] fun z ↦ (logDeriv Y (z + σ) - logDeriv Y z) + Cst := by
    filter_upwards [hY.mixed w] with u hu
    linear_combination hu
  have hmeroShift : MeromorphicAt (fun z ↦ logDeriv Y (z + τ + σ) - logDeriv Y (z + τ)) w := by
    have h₁ : MeromorphicAt (fun z ↦ logDeriv Y (z + τ + σ)) w := by
      have h' : MeromorphicAt (fun z ↦ logDeriv Y (z + (τ + σ))) w :=
        meromorphicAt_comp_add.mpr (hFmero (w + (τ + σ)) (Set.mem_univ _))
      have hfun : (fun z ↦ logDeriv Y (z + (τ + σ))) = fun z ↦ logDeriv Y (z + τ + σ) := by
        funext z
        rw [show z + (τ + σ) = z + τ + σ by ring]
      rwa [hfun] at h'
    have h₂ : MeromorphicAt (fun z ↦ logDeriv Y (z + τ)) w :=
      meromorphicAt_comp_add.mpr (hFmero (w + τ) (Set.mem_univ _))
    exact h₁.sub h₂
  rw [hshift, laurentCoeff_congr hmeroShift hev ℓ,
    laurentCoeff_add_const (hGmero w (Set.mem_univ w)) Cst hℓ]

/-- **The shift order of a triptic source is `τ`-invariant.**  This is the exact translation of the
mixed germ constraint into a statement about orders. -/
theorem shiftOrder_add_tau_of_source (hY : TripticMultiplicativeSource τ σ Y Cst) (w : ℂ) :
    shiftOrder Y σ (w + τ) = shiftOrder Y σ w := by
  have h₁ := laurentCoeff_shiftDiff_logDeriv hY.mero hY.finOrd σ (w + τ)
  have h₂ := laurentCoeff_shiftDiff_logDeriv hY.mero hY.finOrd σ w
  have h := laurentCoeff_shiftDiff_logDeriv_add_tau hY w (by norm_num : (-1 : ℤ) < 0)
  rw [h₁, h₂] at h
  exact_mod_cast h

/-- The residue coefficient of the logarithmic shift difference is `1`-periodic. -/
theorem laurentCoeff_shiftDiff_logDeriv_add_one
    (hY : TripticMultiplicativeSource τ σ Y Cst) (w : ℂ) (ℓ : ℤ) :
    laurentCoeff (fun z ↦ logDeriv Y (z + σ) - logDeriv Y z) (w + 1) ℓ
      = laurentCoeff (fun z ↦ logDeriv Y (z + σ) - logDeriv Y z) w ℓ := by
  have hper : ∀ z : ℂ, logDeriv Y (z + 1) = logDeriv Y z := fun z ↦
    logDeriv_of_periodic hY.periodic z
  have hfun : (fun z : ℂ ↦ logDeriv Y (z + 1 + σ) - logDeriv Y (z + 1))
      = fun z ↦ logDeriv Y (z + σ) - logDeriv Y z := by
    funext z
    rw [show z + 1 + σ = z + σ + 1 by ring, hper (z + σ), hper z]
  calc laurentCoeff (fun z ↦ logDeriv Y (z + σ) - logDeriv Y z) (w + 1) ℓ
      = laurentCoeff (fun z ↦ logDeriv Y (z + 1 + σ) - logDeriv Y (z + 1)) w ℓ := by
        rw [← laurentCoeff_comp_add (fun z ↦ logDeriv Y (z + σ) - logDeriv Y z) w 1 ℓ]
    _ = laurentCoeff (fun z ↦ logDeriv Y (z + σ) - logDeriv Y z) w ℓ := by rw [hfun]

/-- **Every member of the class has finite shift-order support along every orbit.** -/
theorem finiteShiftSupport_of_source (hY : TripticMultiplicativeSource τ σ Y Cst)
    (hτ : 0 < τ.im) (hindep : IndepPeriods τ σ) (p : ℂ) :
    FiniteShiftSupport Y σ p := by
  classical
  have hFmero : MeromorphicOn (logDeriv Y) (Set.univ : Set ℂ) := fun z _ ↦
    ((hY.mero z (Set.mem_univ z)).deriv).div (hY.mero z (Set.mem_univ z))
  have hGmero : MeromorphicOn (fun z ↦ logDeriv Y (z + σ) - logDeriv Y z)
      (Set.univ : Set ℂ) := fun z _ ↦
    (meromorphicAt_comp_add.mpr (hFmero (z + σ) (Set.mem_univ _))).sub
      (hFmero z (Set.mem_univ z))
  have hfinset := finite_setOf_laurentCoeff_ne_zero_orbit hGmero
    (by norm_num : (-1 : ℤ) < 0) hτ
    (fun a ↦ laurentCoeff_shiftDiff_logDeriv_add_one hY a (-1))
    (fun a ↦ laurentCoeff_shiftDiff_logDeriv_add_tau hY a (by norm_num : (-1 : ℤ) < 0))
    (indepSwap_of_indepPeriods hindep) p
  refine hfinset.subset ?_
  intro m hm
  simp only [Set.mem_setOf_eq] at hm ⊢
  rw [laurentCoeff_shiftDiff_logDeriv hY.mero hY.finOrd]
  exact_mod_cast hm

/-! ### The period group and the orbit space -/

/-- **The triptic period group** `H₃ = ℤ + ℤτ + ℤσ` as an additive subgroup of `ℂ`. -/
def tripticPeriodGroup (τ σ : ℂ) : AddSubgroup ℂ where
  carrier := {p | PeriodGroupMem τ σ p}
  zero_mem' := ⟨0, 0, 0, by push_cast; ring⟩
  add_mem' := by
    rintro x y ⟨c, d, e, rfl⟩ ⟨c', d', e', rfl⟩
    exact ⟨c + c', d + d', e + e', by push_cast; ring⟩
  neg_mem' := by
    rintro x ⟨c, d, e, rfl⟩
    exact ⟨-c, -d, -e, by push_cast; ring⟩

theorem mem_tripticPeriodGroup_iff {p : ℂ} :
    p ∈ tripticPeriodGroup τ σ ↔ PeriodGroupMem τ σ p := Iff.rfl

/-- **The orbital charge is constant on `H₃`-classes.** -/
theorem tripticOrbitCharge_eq_of_sub_mem (hY : TripticMultiplicativeSource τ σ Y Cst)
    {p q : ℂ} (h : p - q ∈ tripticPeriodGroup τ σ) :
    tripticOrbitCharge Y σ p = tripticOrbitCharge Y σ q := by
  obtain ⟨c, d, e, hcde⟩ := h
  have hp : p = q + (c : ℂ) * 1 + (d : ℂ) * τ + (e : ℂ) * σ := by
    have : p - q = (c : ℂ) + (d : ℂ) * τ + (e : ℂ) * σ := hcde
    linear_combination this
  rw [hp]
  exact tripticOrbitCharge_of_periodGroup hY.periodic
    (fun w ↦ shiftOrder_add_tau_of_source hY w)
    (fun r ↦ tripticOrbitCharge_shift Y σ r) c d e

/-- The orbital charge, transported to the orbit space `ℂ ⧸ H₃` through a choice of
representatives.  For a member of the class the choice is immaterial, by
`tripticChargeClass_mk`. -/
def tripticChargeClass (Y : ℂ → ℂ) (τ σ : ℂ) : (ℂ ⧸ tripticPeriodGroup τ σ) → ℤ :=
  fun g ↦ tripticOrbitCharge Y σ (Quotient.out g)

/-- **The transported charge of a class is the charge of any representative.** -/
theorem tripticChargeClass_mk (hY : TripticMultiplicativeSource τ σ Y Cst) (p : ℂ) :
    tripticChargeClass Y τ σ (QuotientAddGroup.mk p) = tripticOrbitCharge Y σ p := by
  refine tripticOrbitCharge_eq_of_sub_mem hY ?_
  have hout : (QuotientAddGroup.mk (Quotient.out (QuotientAddGroup.mk (s := tripticPeriodGroup τ σ) p)) :
      ℂ ⧸ tripticPeriodGroup τ σ) = QuotientAddGroup.mk p :=
    QuotientAddGroup.out_eq' _
  have hmem := (QuotientAddGroup.eq
    (s := tripticPeriodGroup τ σ)
    (a := Quotient.out (QuotientAddGroup.mk (s := tripticPeriodGroup τ σ) p)) (b := p)).mp hout
  have := neg_mem (s := tripticPeriodGroup τ σ) hmem
  simpa [neg_add_rev, sub_eq_add_neg, add_comm] using this

/-! ### Finite support on the orbit space -/

/-- Every point of the plane is carried into the compact parallelogram of the lattice `ℤ + ℤτ`
by integer steps in `1` and `τ`. -/
theorem exists_lattice_reduction (hτ : 0 < τ.im) (x : ℂ) :
    ∃ c d : ℤ, ‖x + (c : ℂ) + (d : ℂ) * τ‖ ≤ 1 + ‖τ‖ := by
  set d : ℤ := -⌊x.im / τ.im⌋ with hd
  set y : ℂ := x + (d : ℂ) * τ with hy
  have hyim : 0 ≤ y.im ∧ y.im ≤ τ.im := by
    have him : y.im = x.im - (⌊x.im / τ.im⌋ : ℝ) * τ.im := by
      simp only [hy, hd, Complex.add_im, Complex.mul_im, Complex.neg_re, Complex.neg_im,
        Complex.intCast_re, Complex.intCast_im, Int.cast_neg]
      ring
    constructor
    · rw [him]
      exact Int.sub_floor_div_mul_nonneg x.im hτ
    · rw [him]
      have hlt := Int.lt_floor_add_one (x.im / τ.im)
      have := (div_lt_iff₀ hτ).mp hlt
      nlinarith [hτ]
  set c : ℤ := -⌊y.re⌋ with hc
  set v : ℂ := y + (c : ℂ) with hv
  have hvre : 0 ≤ v.re ∧ v.re ≤ 1 := by
    have hre : v.re = y.re - (⌊y.re⌋ : ℝ) := by
      simp only [hv, hc, Complex.add_re, Complex.neg_re, Complex.intCast_re, Int.cast_neg]
      ring
    constructor
    · rw [hre]
      have := Int.floor_le y.re
      linarith
    · rw [hre]
      have := Int.lt_floor_add_one y.re
      linarith
  have hvim : v.im = y.im := by
    simp [hv, Complex.add_im, Complex.intCast_im]
  refine ⟨c, d, ?_⟩
  have hxcd : x + (c : ℂ) + (d : ℂ) * τ = v := by
    simp only [hv, hy]
    ring
  rw [hxcd]
  calc ‖v‖ ≤ |v.re| + |v.im| := Complex.norm_le_abs_re_add_abs_im v
    _ ≤ 1 + ‖τ‖ := by
        have h₁ : |v.re| ≤ 1 := abs_le.mpr ⟨by linarith [hvre.1], hvre.2⟩
        have h₂ : |v.im| ≤ ‖τ‖ := by
          rw [hvim]
          have hy₂ : |y.im| ≤ τ.im := abs_le.mpr ⟨by linarith [hyim.1], hyim.2⟩
          exact hy₂.trans ((le_abs_self τ.im).trans (Complex.abs_im_le_norm τ))
        linarith

/-- **The transported charge has finite support.**  Every charged class has a representative with
nonzero shift order inside a compact fundamental region of the lattice `ℤ + ℤτ`, and the
shift-order support meets a compact set finitely. -/
theorem finite_support_tripticChargeClass (hY : TripticMultiplicativeSource τ σ Y Cst)
    (hτ : 0 < τ.im) :
    (Function.support (tripticChargeClass Y τ σ)).Finite := by
  classical
  set K : Set ℂ := Metric.closedBall (0 : ℂ) (1 + ‖τ‖) with hK
  have hKc : IsCompact K := isCompact_closedBall 0 (1 + ‖τ‖)
  have hSfin : {w | w ∈ K ∧ shiftOrder Y σ w ≠ 0}.Finite :=
    finite_setOf_shiftOrder_ne_zero hY.mero hY.finOrd hKc
  refine (hSfin.image (QuotientAddGroup.mk (s := tripticPeriodGroup τ σ))).subset ?_
  intro g hg
  simp only [Function.mem_support, tripticChargeClass] at hg
  set p : ℂ := Quotient.out g with hp
  have hex : ∃ m : ℤ, shiftOrder Y σ (p + (m : ℂ) * σ) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hg (by
      rw [tripticOrbitCharge]
      exact finsum_eq_zero_of_forall_eq_zero hcon)
  obtain ⟨m, hm⟩ := hex
  obtain ⟨c, d, hcd⟩ := exists_lattice_reduction hτ (p + (m : ℂ) * σ)
  set v : ℂ := p + (m : ℂ) * σ + (c : ℂ) + (d : ℂ) * τ with hv
  have hvorder : shiftOrder Y σ v ≠ 0 := by
    have hone : ∀ r : ℂ, shiftOrder Y σ (r + 1) = shiftOrder Y σ r := fun r ↦
      shiftOrder_of_period hY.periodic r
    have hτinv : ∀ r : ℂ, shiftOrder Y σ (r + τ) = shiftOrder Y σ r := fun r ↦
      shiftOrder_add_tau_of_source hY r
    have h₁ : shiftOrder Y σ (p + (m : ℂ) * σ + (c : ℂ) + (d : ℂ) * τ)
        = shiftOrder Y σ (p + (m : ℂ) * σ + (c : ℂ)) :=
      eq_of_add_zsmul (f := fun r ↦ shiftOrder Y σ r) (p := τ) hτinv
        (p + (m : ℂ) * σ + (c : ℂ)) d
    have h₂ : shiftOrder Y σ (p + (m : ℂ) * σ + (c : ℂ))
        = shiftOrder Y σ (p + (m : ℂ) * σ) := by
      have h₂' := eq_of_add_zsmul (f := fun r ↦ shiftOrder Y σ r) (p := 1) hone
        (p + (m : ℂ) * σ) c
      rwa [mul_one] at h₂'
    rw [hv, h₁, h₂]
    exact hm
  refine ⟨v, ⟨?_, hvorder⟩, ?_⟩
  · simpa [hK, Metric.mem_closedBall, dist_eq_norm] using hcd
  · have hclass : (QuotientAddGroup.mk v : ℂ ⧸ tripticPeriodGroup τ σ)
        = QuotientAddGroup.mk p := by
      rw [QuotientAddGroup.eq]
      refine ⟨-c, -d, -m, ?_⟩
      push_cast
      simp only [hv]
      ring
    rw [hclass, hp, QuotientAddGroup.out_eq']

/-! ### The divisor as a finitely supported function on the orbit space -/

/-- **The integral orbit divisor of a triptic source**, as an element of
`ℤ[ℂ/H₃] = (ℂ ⧸ H₃) →₀ ℤ`. -/
def tripticDivisor (Y : ℂ → ℂ) (τ σ : ℂ)
    (hfin : (Function.support (tripticChargeClass Y τ σ)).Finite) :
    (ℂ ⧸ tripticPeriodGroup τ σ) →₀ ℤ :=
  Finsupp.ofSupportFinite _ hfin

/-- **The divisor coefficient at a class is the charge at any representative.** -/
theorem tripticDivisor_mk (hY : TripticMultiplicativeSource τ σ Y Cst)
    (hfin : (Function.support (tripticChargeClass Y τ σ)).Finite) (p : ℂ) :
    tripticDivisor Y τ σ hfin (QuotientAddGroup.mk p) = tripticOrbitCharge Y σ p := by
  have : tripticDivisor Y τ σ hfin (QuotientAddGroup.mk p)
      = tripticChargeClass Y τ σ (QuotientAddGroup.mk p) := rfl
  rw [this, tripticChargeClass_mk hY]

end

end GaloisForLFunctions.HTGeometry
