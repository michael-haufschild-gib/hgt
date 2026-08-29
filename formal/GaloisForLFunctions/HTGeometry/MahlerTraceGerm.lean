import GaloisForLFunctions.HTGeometry.MahlerBaseNoTelescoper
import GaloisForLFunctions.HTGeometry.ScaledDerivationTransfer

/-!
# The reduced-trace germ of an ultrametric spectrum

The reduced one-particle trace of the `p`-adic Neumann-to-Dirichlet spectrum is the lacunary
series `(p−2)w + (p−1)²·Σ_{n≥1} p^(n−1) w^(p^n)`, which is the unique formal solution of the
inhomogeneous Mahler equation `K(w) = (p−2)w + w^p + p·K(w^p)`.  Multiplying by the twisting
coordinate turns that equation into an additive shift for the Mahler substitution, whose increment
lies in the two-variable perfect base.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped RatFunc

noncomputable section

variable {k : Type*} [Field k]

/-- The powers of `p` as an order embedding of the exponent lattice. -/
def natPowEmb (p : ℕ) (hp : 1 < p) : ℕ ↪o ℚ :=
  OrderEmbedding.ofStrictMono (fun i => ((p : ℚ)) ^ i)
    (fun _ _ hij => pow_lt_pow_right₀ (by exact_mod_cast hp) hij)

@[simp]
theorem natPowEmb_apply (p : ℕ) (hp : 1 < p) (i : ℕ) :
    natPowEmb p hp i = ((p : ℚ)) ^ i := rfl

/-- A Hahn series with natural exponents is just a coefficient sequence. -/
def natHahn (f : ℕ → k) : HahnSeries ℕ k where
  coeff := f
  isPWO_support' := Set.IsPWO.of_linearOrder _

@[simp]
theorem coeff_natHahn (f : ℕ → k) (i : ℕ) : (natHahn f).coeff i = f i := rfl

/-- The coefficients of the reduced trace. -/
def traceCoeffSeq (p : ℕ) : ℕ → k
  | 0 => ((p : k)) - 2
  | (i + 1) => ((p : k)) ^ i * (((p : k)) - 1) ^ 2

/-- **The reduced one-particle trace** of the `p`-adic Neumann-to-Dirichlet spectrum. -/
def traceSeries (p : ℕ) (hp : 1 < p) : HahnSeries ℚ k :=
  HahnSeries.embDomain (natPowEmb p hp) (natHahn (traceCoeffSeq (k := k) p))

theorem coeff_traceSeries_pow (p : ℕ) (hp : 1 < p) (i : ℕ) :
    (traceSeries (k := k) p hp).coeff (((p : ℚ)) ^ i) = traceCoeffSeq p i := by
  have h := HahnSeries.embDomain_coeff (f := natPowEmb p hp)
    (x := natHahn (traceCoeffSeq (k := k) p)) (a := i)
  rw [natPowEmb_apply] at h
  exact h

theorem coeff_traceSeries_of_not_pow (p : ℕ) (hp : 1 < p) {γ : ℚ}
    (hγ : ∀ i : ℕ, ((p : ℚ)) ^ i ≠ γ) : (traceSeries (k := k) p hp).coeff γ = 0 := by
  refine HahnSeries.embDomain_notin_range ?_
  rintro ⟨i, hi⟩
  exact hγ i hi

theorem qPow_injective {p : ℕ} (hp : 1 < p) :
    Function.Injective (fun i : ℕ => ((p : ℚ)) ^ i) :=
  (natPowEmb p hp).injective

theorem qPow_eq_one_iff {p : ℕ} (hp : 1 < p) (i : ℕ) : ((p : ℚ)) ^ i = 1 ↔ i = 0 := by
  constructor
  · intro h
    exact qPow_injective hp (by simpa using h)
  · rintro rfl
    rw [pow_zero]

theorem qPow_eq_self_iff {p : ℕ} (hp : 1 < p) (i : ℕ) : ((p : ℚ)) ^ i = (p : ℚ) ↔ i = 1 := by
  constructor
  · intro h
    exact qPow_injective hp (by simpa using h)
  · rintro rfl
    rw [pow_one]

theorem qPow_div (p : ℕ) (hp : 1 < p) (i : ℕ) :
    ((p : ℚ)) ^ (i + 1) / (p : ℚ) = ((p : ℚ)) ^ i := by
  have hpQ : ((p : ℚ)) ≠ 0 := by
    have : 0 < p := by omega
    exact_mod_cast this.ne'
  rw [pow_succ, mul_div_cancel_right₀ _ hpQ]

theorem qPow_zero_div_not_pow (p : ℕ) (hp : 1 < p) (i : ℕ) :
    ((p : ℚ)) ^ i ≠ (1 : ℚ) / (p : ℚ) := by
  have hp1 : (1 : ℚ) < (p : ℚ) := by exact_mod_cast hp
  intro hcon
  have h1 : (1 : ℚ) ≤ ((p : ℚ)) ^ i := one_le_pow₀ (le_of_lt hp1)
  rw [hcon] at h1
  rw [le_div_iff₀ (by linarith)] at h1
  linarith

/-- The Mahler coordinate as a Hahn series. -/
def wSeries (k : Type*) [Field k] : HahnSeries ℚ k := HahnSeries.single (1 : ℚ) 1

theorem wSeries_pow (k : Type*) [Field k] (p : ℕ) :
    (wSeries k) ^ p = HahnSeries.single ((p : ℚ)) 1 := by
  rw [wSeries, HahnSeries.single_pow, one_pow]
  congr 1
  simp

theorem coeff_wSeries (k : Type*) [Field k] (γ : ℚ) :
    (wSeries k).coeff γ = if γ = 1 then 1 else 0 := by
  rw [wSeries]
  by_cases h : γ = 1
  · subst h
    rw [HahnSeries.coeff_single_same, if_pos rfl]
  · rw [if_neg h, HahnSeries.coeff_single_of_ne h]

theorem coeff_wSeries_pow (k : Type*) [Field k] (p : ℕ) (γ : ℚ) :
    ((wSeries k) ^ p).coeff γ = if γ = (p : ℚ) then 1 else 0 := by
  rw [wSeries_pow]
  by_cases h : γ = (p : ℚ)
  · subst h
    rw [HahnSeries.coeff_single_same, if_pos rfl]
  · rw [if_neg h, HahnSeries.coeff_single_of_ne h]

set_option maxHeartbeats 1000000 in
/-- **The reduced trace satisfies its Mahler equation** `K(w) = (p−2)w + w^p + p·K(w^p)`. -/
theorem traceSeries_mahler_equation [CharZero k] (p : ℕ) (hp : 1 < p) :
    traceSeries (k := k) p hp
      = HahnSeries.C (((p : k)) - 2) * wSeries k + (wSeries k) ^ p
        + HahnSeries.C ((p : k)) * mahlerHom p (by omega) (traceSeries (k := k) p hp) := by
  refine HahnSeries.coeff_inj.mp (funext fun γ => ?_)
  rw [HahnSeries.coeff_add, HahnSeries.coeff_add, coeff_C_mul_hahn, coeff_C_mul_hahn,
    coeff_wSeries, coeff_wSeries_pow, coeff_mahlerHom p hp]
  by_cases hγ : ∃ i : ℕ, ((p : ℚ)) ^ i = γ
  · obtain ⟨i, rfl⟩ := hγ
    rw [coeff_traceSeries_pow]
    cases i with
    | zero =>
        rw [pow_zero, if_pos rfl, if_neg (by
          intro hcon
          have : ((p : ℚ)) ^ (0 : ℕ) = (p : ℚ) := by rw [pow_zero]; exact hcon
          have := (qPow_eq_self_iff hp 0).mp this
          omega),
          coeff_traceSeries_of_not_pow p hp (fun j => by
            have := qPow_zero_div_not_pow p hp j
            simpa using this)]
        rw [traceCoeffSeq]
        ring
    | succ i =>
        rw [if_neg (by
          intro hcon
          have := (qPow_eq_one_iff hp (i + 1)).mp hcon
          omega), qPow_div p hp i, coeff_traceSeries_pow]
        cases i with
        | zero =>
            rw [if_pos (by rw [pow_one]), traceCoeffSeq, traceCoeffSeq]
            ring
        | succ i =>
            rw [if_neg (by
              intro hcon
              have := (qPow_eq_self_iff hp (i + 1 + 1)).mp hcon
              omega), traceCoeffSeq, traceCoeffSeq, pow_succ]
            ring
  · push Not at hγ
    rw [coeff_traceSeries_of_not_pow p hp hγ,
      if_neg (fun hcon => hγ 0 (by rw [pow_zero, hcon])),
      if_neg (fun hcon => hγ 1 (by rw [pow_one, hcon])),
      coeff_traceSeries_of_not_pow p hp (fun j hcon => hγ (j + 1) (by
        rw [pow_succ]
        have hpQ : ((p : ℚ)) ≠ 0 := by
          have : 0 < p := by omega
          exact_mod_cast this.ne'
        field_simp at hcon ⊢
        linarith [hcon]))]
    ring

/-! ## The germ in the ambient field -/

/-- The reduced trace multiplied by the twisting coordinate. -/
def traceGerm (p : ℕ) (hp : 1 < p) : MahlerAmbient k :=
  HahnSeries.C (traceSeries (k := k) p hp) * mahlerCoordInv k

theorem coeff_C_hahn (U : HahnSeries ℚ k) (n : ℤ) :
    (HahnSeries.C U : MahlerAmbient k).coeff n = if n = 0 then U else 0 := by
  by_cases h : n = 0
  · subst h
    rw [if_pos rfl, HahnSeries.C_apply, HahnSeries.coeff_single_same]
  · rw [if_neg h, HahnSeries.C_apply, HahnSeries.coeff_single_of_ne h]

theorem mahlerDilation_C_hahn [CharZero k] (p : ℕ) (hp : 1 < p) (U : HahnSeries ℚ k) :
    mahlerDilation p hp (HahnSeries.C U : MahlerAmbient k)
      = HahnSeries.C (mahlerHom p (by omega) U) := by
  refine HahnSeries.coeff_inj.mp (funext fun n => ?_)
  rw [coeff_mahlerDilation, coeff_C_hahn, coeff_C_hahn]
  by_cases h : n = 0
  · rw [if_pos h, h, zpow_zero, one_mul, if_pos rfl]
  · rw [if_neg h, if_neg h, map_zero, mul_zero]

theorem wCoord_coe (p : ℕ) (hp : 1 < p) :
    ((wCoord (k := k) p hp : perfectBase (k := k) p hp) : HahnSeries ℚ k) = wSeries k := by
  show ratFuncToHahn (RatFunc.X : RatFunc k) = wSeries k
  rw [ratFuncToHahn, RingHom.coe_comp, Function.comp_apply, algebraMap_ratFuncX, laurentCoord]
  show HahnSeries.embDomain _ (HahnSeries.single (1 : ℤ) (1 : k)) = wSeries k
  rw [HahnSeries.embDomain_single, wSeries]
  norm_num

theorem traceCoeff_zero_coe [CharZero k] (p : ℕ) (hp : 1 < p) :
    ((traceCoeff (k := k) p hp 0 : perfectBase (k := k) p hp) : HahnSeries ℚ k)
      = -(HahnSeries.C (((p : k)) - 2) * wSeries k + (wSeries k) ^ p) := by
  rw [traceCoeff]
  show -(((perfectConst p hp (((p : k)) - 2) * wCoord p hp
      + perfectConst p hp (((p : k)) ^ (0 : ℕ)) * wCoord p hp ^ p :
        perfectBase (k := k) p hp) : HahnSeries ℚ k)) = _
  rw [Subfield.coe_add, Subfield.coe_mul, Subfield.coe_mul, perfectConst_coe, perfectConst_coe,
    wCoord_coe]
  show -(HahnSeries.C (((p : k)) - 2) * wSeries k
    + HahnSeries.C (((p : k)) ^ (0 : ℕ)) * ((wCoord (k := k) p hp : perfectBase (k := k) p hp) :
      HahnSeries ℚ k) ^ p) = _
  rw [wCoord_coe, pow_zero, map_one, one_mul]

theorem mahlerPEmbed_algebraMap_perfect [CharZero k] (p : ℕ) (hp : 1 < p)
    (B : perfectBase (k := k) p hp) :
    mahlerPEmbed k p hp (algebraMap (perfectBase (k := k) p hp) (MahlerPBase k p hp) B)
      = HahnSeries.C (B : HahnSeries ℚ k) := by
  show (hahnMapRingHom ((perfectBase (k := k) p hp).subtype))
      ((algebraMap (RatFunc (perfectBase (k := k) p hp))
        (LaurentSeries (perfectBase (k := k) p hp)))
        (algebraMap (perfectBase (k := k) p hp) (RatFunc (perfectBase (k := k) p hp)) B)) = _
  rw [algebraMap_const_laurentSeries]
  refine HahnSeries.coeff_inj.mp (funext fun n => ?_)
  rw [coeff_hahnMapRingHom, HahnSeries.C_apply]
  by_cases h : n = 0
  · subst h
    rw [HahnSeries.coeff_single_same, HahnSeries.coeff_single_same]
    rfl
  · rw [HahnSeries.coeff_single_of_ne h, HahnSeries.coeff_single_of_ne h, map_zero]

theorem mahlerPEmbed_traceIncrement [CharZero k] (p : ℕ) (hp : 1 < p) :
    mahlerPEmbed k p hp (traceIncrement (k := k) p hp)
      = HahnSeries.C (-(HahnSeries.C (((p : k)) - 2) * wSeries k + (wSeries k) ^ p))
        * mahlerCoordInv k := by
  rw [traceIncrement, map_mul, mahlerPEmbed_algebraMap_perfect, mahlerPEmbed_X_inv,
    traceCoeff_zero_coe]

set_option maxHeartbeats 1000000 in
/-- **The trace germ is an additive primitive** of a base increment for the Mahler
substitution. -/
theorem traceGerm_shift [CharZero k] (p : ℕ) (hp : 1 < p) :
    mahlerDilation p hp (traceGerm (k := k) p hp)
      = traceGerm (k := k) p hp + mahlerPEmbed k p hp (traceIncrement (k := k) p hp) := by
  have hgerm : traceGerm (k := k) p hp
      = HahnSeries.C (traceSeries (k := k) p hp) * mahlerCoordInv k := rfl
  rw [hgerm, map_mul, mahlerDilation_C_hahn, mahlerDilation_mahlerCoordInv,
    mahlerPEmbed_traceIncrement]
  have hkey : (HahnSeries.C (mahlerHom p (by omega : 0 < p) (traceSeries (k := k) p hp))
        : MahlerAmbient k) * HahnSeries.C (HahnSeries.C ((p : k)))
      = HahnSeries.C (traceSeries (k := k) p hp)
        + HahnSeries.C (-(HahnSeries.C (((p : k)) - 2) * wSeries k + (wSeries k) ^ p)) := by
    rw [← map_mul, ← map_add]
    congr 1
    have h := traceSeries_mahler_equation (k := k) p hp
    linear_combination -h
  calc (HahnSeries.C (mahlerHom p (by omega : 0 < p) (traceSeries (k := k) p hp))
        : MahlerAmbient k)
        * (HahnSeries.C (HahnSeries.C ((p : k))) * mahlerCoordInv k)
      = ((HahnSeries.C (mahlerHom p (by omega : 0 < p) (traceSeries (k := k) p hp))
          : MahlerAmbient k) * HahnSeries.C (HahnSeries.C ((p : k)))) * mahlerCoordInv k := by
        ring
    _ = (HahnSeries.C (traceSeries (k := k) p hp)
          + HahnSeries.C (-(HahnSeries.C (((p : k)) - 2) * wSeries k + (wSeries k) ^ p)))
        * mahlerCoordInv k := by rw [hkey]
    _ = HahnSeries.C (traceSeries (k := k) p hp) * mahlerCoordInv k
        + HahnSeries.C (-(HahnSeries.C (((p : k)) - 2) * wSeries k + (wSeries k) ^ p))
          * mahlerCoordInv k := by ring

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- **The reduced one-particle trace of the `p`-adic Neumann-to-Dirichlet spectrum is
hypertranscendental** over the two-variable perfect base, for every `p ≥ 2`. -/
theorem hypertranscendentalOver_traceGerm [CharZero k] (p : ℕ) (hp : 1 < p) :
    letI := perfectAlgebra (k := k) p hp
    letI := perfectDifferential (k := k) p hp
    letI := mahlerPBaseDifferential (k := k) p hp
    letI := mahlerCommDifferential (k := k)
    letI := mahlerPEmbedAlgebra (k := k) p hp
    HypertranscendentalOver (MahlerPBase k p hp) (traceGerm (k := k) p hp) := by
  letI := perfectAlgebra (k := k) p hp
  letI := perfectDifferential (k := k) p hp
  letI := mahlerPBaseDifferential (k := k) p hp
  letI := mahlerCommDifferential (k := k)
  letI := mahlerPEmbedAlgebra (k := k) p hp
  rw [hypertranscendentalOver_iff_differentialIndependent_singleton]
  exact differentialIndependent_of_mahler_primitive p hp (traceGerm (k := k) p hp)
    (traceIncrement (k := k) p hp) (traceGerm_shift p hp)
    (fun c hc y => no_traceIncrement_telescoper p hp c hc y)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- **The reduced trace itself is hypertranscendental for the Euler derivation** `w d/dw`, over
the two-variable perfect base. -/
theorem hypertranscendentalOver_traceSeries_euler [CharZero k] (p : ℕ) (hp : 1 < p) :
    letI := perfectAlgebra (k := k) p hp
    letI := perfectDifferential (k := k) p hp
    letI : Differential (MahlerPBase k p hp) :=
      twoCylinderDifferential (0 : perfectBase (k := k) p hp)
    letI := mahlerDifferential (k := k)
    letI := mahlerPEmbedAlgebra (k := k) p hp
    HypertranscendentalOver (MahlerPBase k p hp)
      (HahnSeries.C (traceSeries (k := k) p hp) : MahlerAmbient k) := by
  letI := perfectAlgebra (k := k) p hp
  letI := perfectDifferential (k := k) p hp
  letI := mahlerPEmbedAlgebra (k := k) p hp
  haveI : CharZero (MahlerAmbient k) :=
    charZero_of_injective_algebraMap (algebraMap k (MahlerAmbient k)).injective
  intro hDA
  have hcompatθ : ∀ y : MahlerPBase k p hp,
      (mahlerDifferential (k := k)).deriv (algebraMap (MahlerPBase k p hp) (MahlerAmbient k) y)
        = algebraMap (MahlerPBase k p hp) (MahlerAmbient k)
          ((twoCylinderDifferential (0 : perfectBase (k := k) p hp)).deriv y) :=
    fun y => (mahlerPEmbed_twoCylDerivation p hp y).symm
  have hcompatδ : ∀ y : MahlerPBase k p hp,
      (mahlerCommDifferential (k := k)).deriv
          (algebraMap (MahlerPBase k p hp) (MahlerAmbient k) y)
        = algebraMap (MahlerPBase k p hp) (MahlerAmbient k)
          ((mahlerPBaseDifferential (k := k) p hp).deriv y) :=
    fun y => (mahlerPEmbed_mahlerPBaseDeriv p hp y).symm
  have hscale : ∀ f : MahlerAmbient k,
      (mahlerCommDifferential (k := k)).deriv f
        = algebraMap (MahlerPBase k p hp) (MahlerAmbient k) ((RatFunc.X : MahlerPBase k p hp)⁻¹)
          * (mahlerDifferential (k := k)).deriv f := by
    intro f
    show mahlerCommDeriv f = mahlerPEmbed k p hp ((RatFunc.X : MahlerPBase k p hp)⁻¹)
      * mahlerAmbientDeriv f
    rw [mahlerPEmbed_X_inv, mahlerCommDeriv_apply]
  have h1 := differentialAlgebraicOver_base_mul
    (K := MahlerPBase k p hp) (L := MahlerAmbient k)
    (twoCylinderDifferential (0 : perfectBase (k := k) p hp)) (mahlerDifferential (k := k))
    ((RatFunc.X : MahlerPBase k p hp)⁻¹) hcompatθ hDA
  have h2 := differentialAlgebraicOver_scaled
    (K := MahlerPBase k p hp) (L := MahlerAmbient k)
    (mahlerPBaseDifferential (k := k) p hp)
    (twoCylinderDifferential (0 : perfectBase (k := k) p hp))
    (mahlerCommDifferential (k := k)) (mahlerDifferential (k := k))
    ((RatFunc.X : MahlerPBase k p hp)⁻¹) hcompatδ hcompatθ hscale h1
  have hgerm : algebraMap (MahlerPBase k p hp) (MahlerAmbient k)
        ((RatFunc.X : MahlerPBase k p hp)⁻¹)
        * (HahnSeries.C (traceSeries (k := k) p hp) : MahlerAmbient k)
      = traceGerm (k := k) p hp := by
    show mahlerPEmbed k p hp ((RatFunc.X : MahlerPBase k p hp)⁻¹)
      * (HahnSeries.C (traceSeries (k := k) p hp) : MahlerAmbient k) = _
    rw [mahlerPEmbed_X_inv, traceGerm, mul_comm]
  rw [hgerm] at h2
  exact hypertranscendentalOver_traceGerm (k := k) p hp h2

end

end GaloisForLFunctions.HTGeometry
