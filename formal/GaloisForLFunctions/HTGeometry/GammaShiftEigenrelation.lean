import GaloisForLFunctions.HTGeometry.HolderShiftElimination

/-!
# No eigenrelation for the jet substitution: the Γ-functional-equation obstruction

The Γ-power elimination behind the transfer `ψ hypertranscendental ⟹ Γ hypertranscendental`
terminates in a difference eigenrelation: two nonzero jet polynomials `f, g` over `ℂ(X)`
with `σ(f)·g = Xᵉ·f·σ(g)`, `e ≥ 1`, where `σ` is the digamma jet substitution
(`jetTranslate`).  This module refutes it.

Reduced to relatively prime parts, the substitution — invertible (`jetTranslateInv`) and
total-degree preserving — forces `σ(f) ∣ f` and `σ(g) ∣ g`; degree multiplicativity over a
domain makes both quotients scalars, so the top-layer coefficients satisfy
`a(X+1)/a(X) = Xᵉ·b(X+1)/b(X)` in `ℂ(X)`.  Cross-multiplied, the degrees of the two sides
differ by exactly `e` — the degree obstruction of the Γ functional equation
`Γ(s+1) = s·Γ(s)`, which admits no rational solution.

* `ratShiftInv`, `jetTranslateInv` — the inverse shift and inverse jet substitution.
* `totalDegree_jetTranslate`, `jetTranslate_injective` — degree preservation, injectivity.
* `ratShift_eq_X_pow_mul_eq_zero` — `r(X+1) = Xᵉ·r(X)`, `e ≥ 1`, forces `r = 0`.
* `no_shift_eigenrelation` — the eigenrelation refutation.
-/

noncomputable section

namespace GaloisForLFunctions

/-! ## The inverse shift -/

section InvShift

open Polynomial nonZeroDivisors

theorem comp_X_sub_C_one_ne_zero {p : Polynomial ℂ} (hp : p ≠ 0) :
    p.comp (X - C 1) ≠ 0 := by
  intro h0
  exact hp ((Polynomial.comp_eq_zero_iff.mp h0).resolve_right
    (fun hh => by
      have := hh.2
      have hco := congrArg (fun r => Polynomial.coeff r 1) this
      simp at hco))

/-- The inverse unit shift `p(X) ↦ p(X−1)`, valued in the rational-function field. -/
def shiftCompHomInv : Polynomial ℂ →+* RatFunc ℂ :=
  (algebraMap (Polynomial ℂ) (RatFunc ℂ)).comp
    (Polynomial.eval₂RingHom Polynomial.C (X - C 1))

theorem shiftCompHomInv_apply (p : Polynomial ℂ) :
    shiftCompHomInv p = algebraMap (Polynomial ℂ) (RatFunc ℂ) (p.comp (X - C 1)) := rfl

theorem shiftCompHomInv_mem_nonZeroDivisors :
    (Polynomial ℂ)⁰ ≤ (RatFunc ℂ)⁰.comap shiftCompHomInv := by
  intro p hp
  rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
  rw [mem_nonZeroDivisors_iff_ne_zero] at hp
  rw [shiftCompHomInv_apply]
  intro h0
  exact comp_X_sub_C_one_ne_zero hp
    (RatFunc.algebraMap_injective ℂ (by rw [h0, map_zero]))

/-- The inverse unit-shift endomorphism `r(X) ↦ r(X−1)` of the rational-function field. -/
def ratShiftInv : RatFunc ℂ →+* RatFunc ℂ :=
  RatFunc.liftRingHom shiftCompHomInv shiftCompHomInv_mem_nonZeroDivisors

theorem ratShiftInv_algebraMap (p : Polynomial ℂ) :
    ratShiftInv (algebraMap (Polynomial ℂ) (RatFunc ℂ) p)
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (p.comp (X - C 1)) := by
  have h := RatFunc.liftRingHom_apply_div shiftCompHomInv
    shiftCompHomInv_mem_nonZeroDivisors p 1
  simp only [map_one, div_one] at h
  exact h

theorem ratShiftInv_ratShift (r : RatFunc ℂ) : ratShiftInv (ratShift r) = r := by
  have hq : algebraMap (Polynomial ℂ) (RatFunc ℂ) r.denom ≠ 0 :=
    fun h0 => r.denom_ne_zero (RatFunc.algebraMap_injective ℂ (by rw [h0, map_zero]))
  conv_lhs => rw [← RatFunc.num_div_denom r]
  rw [map_div₀, map_div₀, ratShift_algebraMap, ratShift_algebraMap,
    ratShiftInv_algebraMap, ratShiftInv_algebraMap]
  have hcomp : ∀ p : Polynomial ℂ,
      (p.comp (X + C 1)).comp (X - C 1) = p := by
    intro p
    rw [Polynomial.comp_assoc]
    simp
  rw [hcomp, hcomp, RatFunc.num_div_denom]

theorem ratShift_ratShiftInv (r : RatFunc ℂ) : ratShift (ratShiftInv r) = r := by
  have hq : algebraMap (Polynomial ℂ) (RatFunc ℂ) r.denom ≠ 0 :=
    fun h0 => r.denom_ne_zero (RatFunc.algebraMap_injective ℂ (by rw [h0, map_zero]))
  conv_lhs => rw [← RatFunc.num_div_denom r]
  rw [map_div₀, map_div₀, ratShiftInv_algebraMap, ratShiftInv_algebraMap,
    ratShift_algebraMap, ratShift_algebraMap]
  have hcomp : ∀ p : Polynomial ℂ,
      (p.comp (X - C 1)).comp (X + C 1) = p := by
    intro p
    rw [Polynomial.comp_assoc]
    simp
  rw [hcomp, hcomp, RatFunc.num_div_denom]

end InvShift

open MvPolynomial

/-! ## The inverse jet substitution -/

/-- The inverse jet substitution: coefficients shift back, each jet variable translates by
the negated pole part. -/
def jetTranslateInv (m : ℕ) :
    MvPolynomial (Fin m) (RatFunc ℂ) →+* MvPolynomial (Fin m) (RatFunc ℂ) :=
  (MvPolynomial.map ratShiftInv).comp
    ((mvPolynomialBaseTranslation
      (fun j : Fin m => -polePart (j : ℕ))).toAlgHom.toRingHom)

theorem jetTranslateInv_comp_jetTranslate (m : ℕ) :
    (jetTranslateInv m).comp (jetTranslate m) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro k
    simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [jetTranslate_C]
    unfold jetTranslateInv
    rw [RingHom.comp_apply]
    rw [show ((mvPolynomialBaseTranslation
        (fun j : Fin m => -polePart (j : ℕ))).toAlgHom.toRingHom) (C (ratShift k))
        = C (ratShift k) by
      rw [show (C (ratShift k) : MvPolynomial (Fin m) (RatFunc ℂ))
          = algebraMap (RatFunc ℂ) (MvPolynomial (Fin m) (RatFunc ℂ)) (ratShift k)
          from rfl]
      exact (mvPolynomialBaseTranslation _).commutes _]
    rw [MvPolynomial.map_C, ratShiftInv_ratShift]
  · intro j
    simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [jetTranslate_X]
    unfold jetTranslateInv
    rw [RingHom.comp_apply, map_add]
    rw [show ((mvPolynomialBaseTranslation
        (fun j : Fin m => -polePart (j : ℕ))).toAlgHom.toRingHom) (X j)
        = X j + C (-polePart (j : ℕ)) from mvPolynomialBaseTranslation_X _ j]
    rw [show ((mvPolynomialBaseTranslation
        (fun j : Fin m => -polePart (j : ℕ))).toAlgHom.toRingHom) (C (polePart (j : ℕ)))
        = C (polePart (j : ℕ)) by
      rw [show (C (polePart (j : ℕ)) : MvPolynomial (Fin m) (RatFunc ℂ))
          = algebraMap (RatFunc ℂ) (MvPolynomial (Fin m) (RatFunc ℂ)) (polePart (j : ℕ))
          from rfl]
      exact (mvPolynomialBaseTranslation _).commutes _]
    have hcancel : (X j : MvPolynomial (Fin m) (RatFunc ℂ)) + C (-polePart (j : ℕ))
        + C (polePart (j : ℕ)) = X j := by
      rw [map_neg]
      ring
    rw [hcancel, MvPolynomial.map_X]

theorem jetTranslate_comp_jetTranslateInv (m : ℕ) :
    (jetTranslate m).comp (jetTranslateInv m) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro k
    simp only [RingHom.comp_apply, RingHom.id_apply]
    unfold jetTranslateInv
    rw [RingHom.comp_apply]
    rw [show ((mvPolynomialBaseTranslation
        (fun j : Fin m => -polePart (j : ℕ))).toAlgHom.toRingHom) (C k) = C k by
      rw [show (C k : MvPolynomial (Fin m) (RatFunc ℂ))
          = algebraMap (RatFunc ℂ) (MvPolynomial (Fin m) (RatFunc ℂ)) k from rfl]
      exact (mvPolynomialBaseTranslation _).commutes _]
    rw [MvPolynomial.map_C, jetTranslate_C, ratShift_ratShiftInv]
  · intro j
    simp only [RingHom.comp_apply, RingHom.id_apply]
    unfold jetTranslateInv
    rw [RingHom.comp_apply]
    rw [show ((mvPolynomialBaseTranslation
        (fun j : Fin m => -polePart (j : ℕ))).toAlgHom.toRingHom) (X j)
        = X j + C (-polePart (j : ℕ)) from mvPolynomialBaseTranslation_X _ j]
    rw [map_add, MvPolynomial.map_X, MvPolynomial.map_C, map_add, jetTranslate_X,
      jetTranslate_C]
    rw [show ratShift (ratShiftInv (-polePart (j : ℕ))) = -polePart (j : ℕ) from
      ratShift_ratShiftInv _]
    rw [map_neg]
    ring

theorem jetTranslateInv_jetTranslate {m : ℕ} (P : MvPolynomial (Fin m) (RatFunc ℂ)) :
    jetTranslateInv m (jetTranslate m P) = P :=
  RingHom.congr_fun (jetTranslateInv_comp_jetTranslate m) P

theorem jetTranslate_jetTranslateInv {m : ℕ} (P : MvPolynomial (Fin m) (RatFunc ℂ)) :
    jetTranslate m (jetTranslateInv m P) = P :=
  RingHom.congr_fun (jetTranslate_comp_jetTranslateInv m) P

theorem jetTranslate_injective {m : ℕ} :
    Function.Injective (jetTranslate m) :=
  Function.LeftInverse.injective jetTranslateInv_jetTranslate

/-! ## Degree preservation -/

theorem totalDegree_jetTranslate {m : ℕ} (P : MvPolynomial (Fin m) (RatFunc ℂ)) :
    (jetTranslate m P).totalDegree = P.totalDegree := by
  rcases eq_or_ne P 0 with rfl | hP
  · rw [map_zero]
  refine le_antisymm (totalDegree_jetTranslate_le P) ?_
  obtain ⟨β, hβ_mem, hβ_sup⟩ :=
    Finset.exists_mem_eq_sup P.support (MvPolynomial.support_nonempty.mpr hP) degSum
  have hβ : degSum β = P.totalDegree := by
    rw [totalDegree_eq_sup_degSum, hβ_sup]
  have htop : coeff β (jetTranslate m P) = ratShift (coeff β P) :=
    coeff_jetTranslate_of_le_degSum (fun α hα => by
      rw [hβ]
      exact MvPolynomial.le_totalDegree hα)
  have hne : coeff β (jetTranslate m P) ≠ 0 := by
    rw [htop]
    exact fun h0 => (MvPolynomial.mem_support_iff.mp hβ_mem)
      (ratShift_injective (by rw [h0, map_zero]))
  calc P.totalDegree = degSum β := hβ.symm
    _ ≤ (jetTranslate m P).totalDegree :=
        MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hne)

/-! ## The rational degree obstruction -/

/-- **The Γ-functional-equation degree obstruction**: no nonzero rational function satisfies
`r(X+1) = Xᵉ·r(X)` with `e ≥ 1`. -/
theorem ratShift_eq_X_pow_mul_eq_zero {r : RatFunc ℂ} {e : ℕ} (he : 1 ≤ e)
    (h : ratShift r = RatFunc.X ^ e * r) : r = 0 := by
  by_contra hr
  set p := r.num with hp_def
  set q := r.denom with hq_def
  have hp : p ≠ 0 := RatFunc.num_ne_zero hr
  have hq : q ≠ 0 := r.denom_ne_zero
  have hrepr : algebraMap (Polynomial ℂ) (RatFunc ℂ) p
      / algebraMap (Polynomial ℂ) (RatFunc ℂ) q = r := RatFunc.num_div_denom r
  have hqK : algebraMap (Polynomial ℂ) (RatFunc ℂ) q ≠ 0 :=
    fun h0 => hq (RatFunc.algebraMap_injective ℂ (by rw [h0, map_zero]))
  have hqcK : algebraMap (Polynomial ℂ) (RatFunc ℂ)
      (q.comp (Polynomial.X + Polynomial.C 1)) ≠ 0 :=
    fun h0 => comp_X_add_C_one_ne_zero hq
      (RatFunc.algebraMap_injective ℂ (by rw [h0, map_zero]))
  have hcross : p.comp (Polynomial.X + Polynomial.C 1) * q
      = Polynomial.X ^ e * p * q.comp (Polynomial.X + Polynomial.C 1) := by
    apply RatFunc.algebraMap_injective ℂ
    have hshift : algebraMap (Polynomial ℂ) (RatFunc ℂ)
          (p.comp (Polynomial.X + Polynomial.C 1))
        / algebraMap (Polynomial ℂ) (RatFunc ℂ)
          (q.comp (Polynomial.X + Polynomial.C 1))
        = RatFunc.X ^ e * (algebraMap (Polynomial ℂ) (RatFunc ℂ) p
            / algebraMap (Polynomial ℂ) (RatFunc ℂ) q) := by
      rw [← ratShift_algebraMap, ← ratShift_algebraMap, ← map_div₀, hrepr, h]
    rw [div_eq_iff hqcK] at hshift
    rw [map_mul, map_mul, map_mul, map_pow, RatFunc.algebraMap_X, hshift]
    field_simp
  have hdeg := congrArg Polynomial.natDegree hcross
  have hpc : p.comp (Polynomial.X + Polynomial.C 1) ≠ 0 := comp_X_add_C_one_ne_zero hp
  have hqc : q.comp (Polynomial.X + Polynomial.C 1) ≠ 0 := comp_X_add_C_one_ne_zero hq
  have hdegX : (Polynomial.X + Polynomial.C (1 : ℂ)).natDegree = 1 := by
    simpa using Polynomial.natDegree_X_add_C (1 : ℂ)
  rw [Polynomial.natDegree_mul hpc hq,
    Polynomial.natDegree_mul (mul_ne_zero (pow_ne_zero e Polynomial.X_ne_zero) hp) hqc,
    Polynomial.natDegree_mul (pow_ne_zero e Polynomial.X_ne_zero) hp,
    Polynomial.natDegree_comp, Polynomial.natDegree_comp, hdegX,
    Polynomial.natDegree_X_pow] at hdeg
  omega

/-! ## The eigenrelation refutation -/

private theorem dvd_of_dvd_C_mul {m : ℕ} {a b : MvPolynomial (Fin m) (RatFunc ℂ)}
    {k : RatFunc ℂ} (hk : k ≠ 0) (h : a ∣ C k * b) : a ∣ b := by
  obtain ⟨t, ht⟩ := h
  refine ⟨C k⁻¹ * t, ?_⟩
  have h2 := congrArg (fun x => C (k⁻¹ : RatFunc ℂ) * x) ht
  rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hk, map_one, one_mul] at h2
  rw [h2]
  ring

/-- **No eigenrelation**: there are no nonzero jet polynomials `f, g` over `ℂ(X)` with
`σ(f)·g = Xᵉ·f·σ(g)` for `e ≥ 1`, `σ` the jet substitution.  Reduced to relatively prime
parts, both `σ(f) ∣ f` and `σ(g) ∣ g` with equal total degrees, so both quotients are
scalars and the top-layer coefficient ratio satisfies the rational Γ functional equation
`r(X+1) = Xᵉ·r(X)` — refuted by the degree count. -/
theorem no_shift_eigenrelation {m : ℕ} {f g : MvPolynomial (Fin m) (RatFunc ℂ)}
    (hf : f ≠ 0) (hg : g ≠ 0) {e : ℕ} (he : 1 ≤ e)
    (h : jetTranslate m f * g
      = C ((RatFunc.X : RatFunc ℂ) ^ e) * (f * jetTranslate m g)) : False := by
  classical
  have hXe : ((RatFunc.X : RatFunc ℂ) ^ e) ≠ 0 := pow_ne_zero _ ratFuncX_ne_zero
  -- reduce to relatively prime parts
  obtain ⟨f₀, g₀, c, hco, hcf, hcg⟩ :=
    UniqueFactorizationMonoid.exists_reduced_factors f hf g
  have hc : c ≠ 0 := fun h0 => hf (by rw [← hcf, h0, zero_mul])
  have hf₀ : f₀ ≠ 0 := fun h0 => hf (by rw [← hcf, h0, mul_zero])
  have hg₀ : g₀ ≠ 0 := fun h0 => hg (by rw [← hcg, h0, mul_zero])
  have hσf₀ : jetTranslate m f₀ ≠ 0 :=
    fun h0 => hf₀ (jetTranslate_injective (by rw [h0, map_zero]))
  have hσg₀ : jetTranslate m g₀ ≠ 0 :=
    fun h0 => hg₀ (jetTranslate_injective (by rw [h0, map_zero]))
  have hσc : jetTranslate m c ≠ 0 :=
    fun h0 => hc (jetTranslate_injective (by rw [h0, map_zero]))
  have h₀ : jetTranslate m f₀ * g₀
      = C ((RatFunc.X : RatFunc ℂ) ^ e) * (f₀ * jetTranslate m g₀) := by
    have hexp : (c * jetTranslate m c) * (jetTranslate m f₀ * g₀)
        = (c * jetTranslate m c)
          * (C ((RatFunc.X : RatFunc ℂ) ^ e) * (f₀ * jetTranslate m g₀)) := by
      have hL : jetTranslate m f * g
          = (c * jetTranslate m c) * (jetTranslate m f₀ * g₀) := by
        rw [← hcf, ← hcg, map_mul]
        ring
      have hR : C ((RatFunc.X : RatFunc ℂ) ^ e) * (f * jetTranslate m g)
          = (c * jetTranslate m c)
            * (C ((RatFunc.X : RatFunc ℂ) ^ e) * (f₀ * jetTranslate m g₀)) := by
        rw [← hcf, ← hcg, map_mul]
        ring
      rw [← hL, ← hR]
      exact h
    exact mul_left_cancel₀ (mul_ne_zero hc hσc) hexp
  -- relative primality transports through the substitution
  have hcoσ : IsRelPrime (jetTranslate m f₀) (jetTranslate m g₀) := by
    intro u huf hug
    have h1 : jetTranslateInv m u ∣ f₀ := by
      have hd := map_dvd (jetTranslateInv m) huf
      rwa [jetTranslateInv_jetTranslate] at hd
    have h2 : jetTranslateInv m u ∣ g₀ := by
      have hd := map_dvd (jetTranslateInv m) hug
      rwa [jetTranslateInv_jetTranslate] at hd
    have hunit := (hco h1 h2).map (jetTranslate m)
    rwa [jetTranslate_jetTranslateInv] at hunit
  -- `σf₀ ∣ f₀`
  have hdvd_f : jetTranslate m f₀ ∣ f₀ := by
    apply dvd_of_dvd_C_mul hXe
    refine IsRelPrime.dvd_of_dvd_mul_right hcoσ ?_
    refine ⟨g₀, ?_⟩
    rw [mul_assoc, ← h₀]
  -- `σg₀ ∣ g₀`
  have hdvd_g : jetTranslate m g₀ ∣ g₀ := by
    have hstep : jetTranslate m g₀ ∣ g₀ * jetTranslate m f₀ := by
      refine ⟨C ((RatFunc.X : RatFunc ℂ) ^ e) * f₀, ?_⟩
      rw [mul_comm g₀ (jetTranslate m f₀), h₀]
      ring
    exact IsRelPrime.dvd_of_dvd_mul_right hcoσ.symm hstep
  -- the quotients are scalars
  obtain ⟨t, ht⟩ := hdvd_f
  have ht0 : t ≠ 0 := fun h0 => hf₀ (by rw [ht, h0, mul_zero])
  have htdeg : t.totalDegree = 0 := by
    have hd := congrArg MvPolynomial.totalDegree ht
    rw [MvPolynomial.totalDegree_mul_of_isDomain hσf₀ ht0,
      totalDegree_jetTranslate] at hd
    omega
  obtain ⟨u, hu⟩ : ∃ u : RatFunc ℂ, t = C u :=
    ⟨coeff 0 t, MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp htdeg⟩
  have hu0 : u ≠ 0 := fun h0 => ht0 (by rw [hu, h0, map_zero])
  obtain ⟨w, hw⟩ := hdvd_g
  have hw0 : w ≠ 0 := fun h0 => hg₀ (by rw [hw, h0, mul_zero])
  have hwdeg : w.totalDegree = 0 := by
    have hd := congrArg MvPolynomial.totalDegree hw
    rw [MvPolynomial.totalDegree_mul_of_isDomain hσg₀ hw0,
      totalDegree_jetTranslate] at hd
    omega
  obtain ⟨v, hv⟩ : ∃ v : RatFunc ℂ, w = C v :=
    ⟨coeff 0 w, MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hwdeg⟩
  have hv0 : v ≠ 0 := fun h0 => hw0 (by rw [hv, h0, map_zero])
  -- the scalar relation `v = Xᵉ·u`
  have hscalar : v = (RatFunc.X : RatFunc ℂ) ^ e * u := by
    have hplug : jetTranslate m f₀ * (jetTranslate m g₀ * C v)
        = C ((RatFunc.X : RatFunc ℂ) ^ e)
          * (jetTranslate m f₀ * C u * jetTranslate m g₀) := by
      rw [← hv, ← hw, ← hu, ← ht]
      exact h₀
    have hcancel : C v * (jetTranslate m f₀ * jetTranslate m g₀)
        = C ((RatFunc.X : RatFunc ℂ) ^ e * u)
          * (jetTranslate m f₀ * jetTranslate m g₀) := by
      rw [map_mul]
      linear_combination hplug
    have := mul_right_cancel₀ (mul_ne_zero hσf₀ hσg₀) hcancel
    exact MvPolynomial.C_injective _ _ this
  -- top-layer coefficients
  obtain ⟨β, hβ_mem, hβ_sup⟩ :=
    Finset.exists_mem_eq_sup f₀.support (MvPolynomial.support_nonempty.mpr hf₀) degSum
  set a := coeff β f₀ with ha_def
  have ha : a ≠ 0 := MvPolynomial.mem_support_iff.mp hβ_mem
  have hβtop : ∀ α ∈ f₀.support, degSum α ≤ degSum β := fun α hα => by
    rw [show degSum β = f₀.totalDegree by rw [totalDegree_eq_sup_degSum, hβ_sup]]
    exact MvPolynomial.le_totalDegree hα
  have ha_rel : a = u * ratShift a := by
    have hco1 := congrArg (coeff β) ht
    rw [hu, mul_comm, coeff_C_mul, coeff_jetTranslate_of_le_degSum hβtop] at hco1
    exact hco1
  obtain ⟨γ, hγ_mem, hγ_sup⟩ :=
    Finset.exists_mem_eq_sup g₀.support (MvPolynomial.support_nonempty.mpr hg₀) degSum
  set b := coeff γ g₀ with hb_def
  have hb : b ≠ 0 := MvPolynomial.mem_support_iff.mp hγ_mem
  have hγtop : ∀ α ∈ g₀.support, degSum α ≤ degSum γ := fun α hα => by
    rw [show degSum γ = g₀.totalDegree by rw [totalDegree_eq_sup_degSum, hγ_sup]]
    exact MvPolynomial.le_totalDegree hα
  have hb_rel : b = v * ratShift b := by
    have hco1 := congrArg (coeff γ) hw
    rw [hv, mul_comm, coeff_C_mul, coeff_jetTranslate_of_le_degSum hγtop] at hco1
    exact hco1
  -- the coefficient ratio satisfies the rational Γ functional equation
  have hσa : ratShift a ≠ 0 := fun h0 => ha (by rw [ha_rel, h0, mul_zero])
  have hσb : ratShift b ≠ 0 := fun h0 => hb (by rw [hb_rel, h0, mul_zero])
  have hshift_a : ratShift a = u⁻¹ * a := by
    field_simp
    linear_combination -ha_rel
  have hshift_b : ratShift b = v⁻¹ * b := by
    field_simp
    linear_combination -hb_rel
  have hratio : ratShift (a / b) = RatFunc.X ^ e * (a / b) := by
    rw [map_div₀, hshift_a, hshift_b, hscalar]
    field_simp
  have hr0 : a / b = 0 := ratShift_eq_X_pow_mul_eq_zero he hratio
  rw [div_eq_zero_iff] at hr0
  rcases hr0 with h' | h'
  · exact ha h'
  · exact hb h'

end GaloisForLFunctions

end
