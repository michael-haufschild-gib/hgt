import GaloisForLFunctions.HTGeometry.ShiftEliminationEngine

/-!
# The eigenrelation obstruction over an abstract shifted field

A difference eigenrelation `σ(f)·g = M·f·σ(g)` between nonzero jet polynomials over a field `K`
carrying an automorphism `σ` is impossible as soon as the scalar equation `σ(r) = M·r` has only the
zero solution.  Reducing `f, g` to relatively prime parts makes `σ(f) ∣ f` and `σ(g) ∣ g`; since the
jet substitution preserves total degree, both quotients are scalars, and the ratio of the
top-layer coefficients solves the scalar equation.
-/

noncomputable section

namespace GaloisForLFunctions

open MvPolynomial

namespace GenericShiftHolder

variable {K : Type*} [Field K] {m : ℕ}

/-! ## The inverse jet substitution -/

/-- The inverse jet substitution: coefficients shift back, each jet variable translates by the
negated increment. -/
def jetTranslateInvGen (τ : K →+* K) (rj : ℕ → K) (m : ℕ) :
    MvPolynomial (Fin m) K →+* MvPolynomial (Fin m) K :=
  (MvPolynomial.map τ).comp
    ((mvPolynomialBaseTranslation (fun j : Fin m => -rj (j : ℕ))).toAlgHom.toRingHom)

theorem jetTranslateInv_comp_jetTranslateGen (σ τ : K →+* K) (rj : ℕ → K)
    (hτσ : ∀ r : K, τ (σ r) = r) :
    (jetTranslateInvGen τ rj m).comp (jetTranslateGen σ rj m) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro k
    simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [jetTranslate_CGen]
    unfold jetTranslateInvGen
    rw [RingHom.comp_apply]
    rw [show ((mvPolynomialBaseTranslation
        (fun j : Fin m => -rj (j : ℕ))).toAlgHom.toRingHom) (C (σ k))
        = C (σ k) by
      rw [show (C (σ k) : MvPolynomial (Fin m) K)
          = algebraMap K (MvPolynomial (Fin m) K) (σ k) from rfl]
      exact (mvPolynomialBaseTranslation _).commutes _]
    rw [MvPolynomial.map_C, hτσ]
  · intro j
    simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [jetTranslate_XGen]
    unfold jetTranslateInvGen
    rw [RingHom.comp_apply, map_add]
    rw [show ((mvPolynomialBaseTranslation
        (fun j : Fin m => -rj (j : ℕ))).toAlgHom.toRingHom) (X j)
        = X j + C (-rj (j : ℕ)) from mvPolynomialBaseTranslation_X _ j]
    rw [show ((mvPolynomialBaseTranslation
        (fun j : Fin m => -rj (j : ℕ))).toAlgHom.toRingHom) (C (rj (j : ℕ)))
        = C (rj (j : ℕ)) by
      rw [show (C (rj (j : ℕ)) : MvPolynomial (Fin m) K)
          = algebraMap K (MvPolynomial (Fin m) K) (rj (j : ℕ)) from rfl]
      exact (mvPolynomialBaseTranslation _).commutes _]
    have hcancel : (X j : MvPolynomial (Fin m) K) + C (-rj (j : ℕ)) + C (rj (j : ℕ))
        = X j := by
      rw [map_neg]
      ring
    rw [hcancel, MvPolynomial.map_X]

theorem jetTranslate_comp_jetTranslateInvGen (σ τ : K →+* K) (rj : ℕ → K)
    (hστ : ∀ r : K, σ (τ r) = r) :
    (jetTranslateGen σ rj m).comp (jetTranslateInvGen τ rj m) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro k
    simp only [RingHom.comp_apply, RingHom.id_apply]
    unfold jetTranslateInvGen
    rw [RingHom.comp_apply]
    rw [show ((mvPolynomialBaseTranslation
        (fun j : Fin m => -rj (j : ℕ))).toAlgHom.toRingHom) (C k) = C k by
      rw [show (C k : MvPolynomial (Fin m) K)
          = algebraMap K (MvPolynomial (Fin m) K) k from rfl]
      exact (mvPolynomialBaseTranslation _).commutes _]
    rw [MvPolynomial.map_C, jetTranslate_CGen, hστ]
  · intro j
    simp only [RingHom.comp_apply, RingHom.id_apply]
    unfold jetTranslateInvGen
    rw [RingHom.comp_apply]
    rw [show ((mvPolynomialBaseTranslation
        (fun j : Fin m => -rj (j : ℕ))).toAlgHom.toRingHom) (X j)
        = X j + C (-rj (j : ℕ)) from mvPolynomialBaseTranslation_X _ j]
    rw [map_add, MvPolynomial.map_X, MvPolynomial.map_C, map_add, jetTranslate_XGen,
      jetTranslate_CGen]
    rw [show σ (τ (-rj (j : ℕ))) = -rj (j : ℕ) from hστ _]
    rw [map_neg]
    ring

theorem jetTranslateInv_jetTranslateGen (σ τ : K →+* K) (rj : ℕ → K)
    (hτσ : ∀ r : K, τ (σ r) = r) (P : MvPolynomial (Fin m) K) :
    jetTranslateInvGen τ rj m (jetTranslateGen σ rj m P) = P :=
  RingHom.congr_fun (jetTranslateInv_comp_jetTranslateGen σ τ rj hτσ) P

theorem jetTranslate_jetTranslateInvGen (σ τ : K →+* K) (rj : ℕ → K)
    (hστ : ∀ r : K, σ (τ r) = r) (P : MvPolynomial (Fin m) K) :
    jetTranslateGen σ rj m (jetTranslateInvGen τ rj m P) = P :=
  RingHom.congr_fun (jetTranslate_comp_jetTranslateInvGen σ τ rj hστ) P

theorem jetTranslateGen_injective (σ τ : K →+* K) (rj : ℕ → K)
    (hτσ : ∀ r : K, τ (σ r) = r) :
    Function.Injective (jetTranslateGen σ rj m) :=
  Function.LeftInverse.injective (jetTranslateInv_jetTranslateGen σ τ rj hτσ)

/-! ## Degree preservation -/

theorem totalDegree_jetTranslateGen (σ : K →+* K) (rj : ℕ → K)
    (P : MvPolynomial (Fin m) K) :
    (jetTranslateGen σ rj m P).totalDegree = P.totalDegree := by
  classical
  rcases eq_or_ne P 0 with rfl | hP
  · rw [map_zero]
  refine le_antisymm (totalDegree_jetTranslate_leGen σ rj P) ?_
  obtain ⟨β, hβ_mem, hβ_sup⟩ :=
    Finset.exists_mem_eq_sup P.support (MvPolynomial.support_nonempty.mpr hP) degSum
  have hβ : degSum β = P.totalDegree := by
    rw [totalDegree_eq_sup_degSumGen, hβ_sup]
  have htop : coeff β (jetTranslateGen σ rj m P) = σ (coeff β P) :=
    coeff_jetTranslate_of_le_degSumGen σ rj (fun α hα => by
      rw [hβ]
      exact MvPolynomial.le_totalDegree hα)
  have hne : coeff β (jetTranslateGen σ rj m P) ≠ 0 := by
    rw [htop]
    exact fun h0 => (MvPolynomial.mem_support_iff.mp hβ_mem)
      (σ.injective (by rw [h0, map_zero]))
  calc P.totalDegree = degSum β := hβ.symm
    _ ≤ (jetTranslateGen σ rj m P).totalDegree :=
        MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hne)

/-! ## The eigenrelation refutation -/

private theorem dvd_of_dvd_C_mulGen {a b : MvPolynomial (Fin m) K} {k : K}
    (hk : k ≠ 0) (h : a ∣ C k * b) : a ∣ b := by
  obtain ⟨t, ht⟩ := h
  refine ⟨C k⁻¹ * t, ?_⟩
  have h2 := congrArg (fun x => C (k⁻¹ : K) * x) ht
  rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hk, map_one, one_mul] at h2
  rw [h2]
  ring

/-- **No eigenrelation**: there are no nonzero jet polynomials `f, g` over `K` with
`σ(f)·g = M·f·σ(g)` once the scalar equation `σ(r) = M·r` has only the zero solution. -/
theorem no_shift_eigenrelationGen (σ τ : K →+* K) (rj : ℕ → K)
    (hτσ : ∀ r : K, τ (σ r) = r) (hστ : ∀ r : K, σ (τ r) = r)
    {M : K} (hM : M ≠ 0) (hobstr : ∀ {r : K}, σ r = M * r → r = 0)
    {f g : MvPolynomial (Fin m) K} (hf : f ≠ 0) (hg : g ≠ 0)
    (h : jetTranslateGen σ rj m f * g = C M * (f * jetTranslateGen σ rj m g)) : False := by
  classical
  -- reduce to relatively prime parts
  obtain ⟨f₀, g₀, c, hco, hcf, hcg⟩ :=
    UniqueFactorizationMonoid.exists_reduced_factors f hf g
  have hc : c ≠ 0 := fun h0 => hf (by rw [← hcf, h0, zero_mul])
  have hf₀ : f₀ ≠ 0 := fun h0 => hf (by rw [← hcf, h0, mul_zero])
  have hg₀ : g₀ ≠ 0 := fun h0 => hg (by rw [← hcg, h0, mul_zero])
  have hσf₀ : jetTranslateGen σ rj m f₀ ≠ 0 :=
    fun h0 => hf₀ (jetTranslateGen_injective σ τ rj hτσ (by rw [h0, map_zero]))
  have hσg₀ : jetTranslateGen σ rj m g₀ ≠ 0 :=
    fun h0 => hg₀ (jetTranslateGen_injective σ τ rj hτσ (by rw [h0, map_zero]))
  have hσc : jetTranslateGen σ rj m c ≠ 0 :=
    fun h0 => hc (jetTranslateGen_injective σ τ rj hτσ (by rw [h0, map_zero]))
  have h₀ : jetTranslateGen σ rj m f₀ * g₀
      = C M * (f₀ * jetTranslateGen σ rj m g₀) := by
    have hexp : (c * jetTranslateGen σ rj m c) * (jetTranslateGen σ rj m f₀ * g₀)
        = (c * jetTranslateGen σ rj m c)
          * (C M * (f₀ * jetTranslateGen σ rj m g₀)) := by
      have hL : jetTranslateGen σ rj m f * g
          = (c * jetTranslateGen σ rj m c) * (jetTranslateGen σ rj m f₀ * g₀) := by
        rw [← hcf, ← hcg, map_mul]
        ring
      have hR : C M * (f * jetTranslateGen σ rj m g)
          = (c * jetTranslateGen σ rj m c)
            * (C M * (f₀ * jetTranslateGen σ rj m g₀)) := by
        rw [← hcf, ← hcg, map_mul]
        ring
      rw [← hL, ← hR]
      exact h
    exact mul_left_cancel₀ (mul_ne_zero hc hσc) hexp
  -- relative primality transports through the substitution
  have hcoσ : IsRelPrime (jetTranslateGen σ rj m f₀) (jetTranslateGen σ rj m g₀) := by
    intro u huf hug
    have h1 : jetTranslateInvGen τ rj m u ∣ f₀ := by
      have hd := map_dvd (jetTranslateInvGen τ rj m) huf
      rwa [jetTranslateInv_jetTranslateGen σ τ rj hτσ] at hd
    have h2 : jetTranslateInvGen τ rj m u ∣ g₀ := by
      have hd := map_dvd (jetTranslateInvGen τ rj m) hug
      rwa [jetTranslateInv_jetTranslateGen σ τ rj hτσ] at hd
    have hunit := (hco h1 h2).map (jetTranslateGen σ rj m)
    rwa [jetTranslate_jetTranslateInvGen σ τ rj hστ] at hunit
  -- `σf₀ ∣ f₀`
  have hdvd_f : jetTranslateGen σ rj m f₀ ∣ f₀ := by
    apply dvd_of_dvd_C_mulGen hM
    refine IsRelPrime.dvd_of_dvd_mul_right hcoσ ?_
    refine ⟨g₀, ?_⟩
    rw [mul_assoc, ← h₀]
  -- `σg₀ ∣ g₀`
  have hdvd_g : jetTranslateGen σ rj m g₀ ∣ g₀ := by
    have hstep : jetTranslateGen σ rj m g₀ ∣ g₀ * jetTranslateGen σ rj m f₀ := by
      refine ⟨C M * f₀, ?_⟩
      rw [mul_comm g₀ (jetTranslateGen σ rj m f₀), h₀]
      ring
    exact IsRelPrime.dvd_of_dvd_mul_right hcoσ.symm hstep
  -- the quotients are scalars
  obtain ⟨t, ht⟩ := hdvd_f
  have ht0 : t ≠ 0 := fun h0 => hf₀ (by rw [ht, h0, mul_zero])
  have htdeg : t.totalDegree = 0 := by
    have hd := congrArg MvPolynomial.totalDegree ht
    rw [MvPolynomial.totalDegree_mul_of_isDomain hσf₀ ht0,
      totalDegree_jetTranslateGen] at hd
    omega
  obtain ⟨u, hu⟩ : ∃ u : K, t = C u :=
    ⟨coeff 0 t, MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp htdeg⟩
  have hu0 : u ≠ 0 := fun h0 => ht0 (by rw [hu, h0, map_zero])
  obtain ⟨w, hw⟩ := hdvd_g
  have hw0 : w ≠ 0 := fun h0 => hg₀ (by rw [hw, h0, mul_zero])
  have hwdeg : w.totalDegree = 0 := by
    have hd := congrArg MvPolynomial.totalDegree hw
    rw [MvPolynomial.totalDegree_mul_of_isDomain hσg₀ hw0,
      totalDegree_jetTranslateGen] at hd
    omega
  obtain ⟨v, hv⟩ : ∃ v : K, w = C v :=
    ⟨coeff 0 w, MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hwdeg⟩
  have hv0 : v ≠ 0 := fun h0 => hw0 (by rw [hv, h0, map_zero])
  -- the scalar relation `v = M·u`
  have hscalar : v = M * u := by
    have hplug : jetTranslateGen σ rj m f₀ * (jetTranslateGen σ rj m g₀ * C v)
        = C M * (jetTranslateGen σ rj m f₀ * C u * jetTranslateGen σ rj m g₀) := by
      rw [← hv, ← hw, ← hu, ← ht]
      exact h₀
    have hcancel : C v * (jetTranslateGen σ rj m f₀ * jetTranslateGen σ rj m g₀)
        = C (M * u) * (jetTranslateGen σ rj m f₀ * jetTranslateGen σ rj m g₀) := by
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
    rw [show degSum β = f₀.totalDegree by rw [totalDegree_eq_sup_degSumGen, hβ_sup]]
    exact MvPolynomial.le_totalDegree hα
  have ha_rel : a = u * σ a := by
    have hco1 := congrArg (coeff β) ht
    rw [hu, mul_comm, coeff_C_mul, coeff_jetTranslate_of_le_degSumGen σ rj hβtop] at hco1
    exact hco1
  obtain ⟨γ, hγ_mem, hγ_sup⟩ :=
    Finset.exists_mem_eq_sup g₀.support (MvPolynomial.support_nonempty.mpr hg₀) degSum
  set b := coeff γ g₀ with hb_def
  have hb : b ≠ 0 := MvPolynomial.mem_support_iff.mp hγ_mem
  have hγtop : ∀ α ∈ g₀.support, degSum α ≤ degSum γ := fun α hα => by
    rw [show degSum γ = g₀.totalDegree by rw [totalDegree_eq_sup_degSumGen, hγ_sup]]
    exact MvPolynomial.le_totalDegree hα
  have hb_rel : b = v * σ b := by
    have hco1 := congrArg (coeff γ) hw
    rw [hv, mul_comm, coeff_C_mul, coeff_jetTranslate_of_le_degSumGen σ rj hγtop] at hco1
    exact hco1
  -- the coefficient ratio solves the scalar equation
  have hσa : σ a ≠ 0 := fun h0 => ha (by rw [ha_rel, h0, mul_zero])
  have hσb : σ b ≠ 0 := fun h0 => hb (by rw [hb_rel, h0, mul_zero])
  have hshift_a : σ a = u⁻¹ * a := by
    field_simp
    linear_combination -ha_rel
  have hshift_b : σ b = v⁻¹ * b := by
    field_simp
    linear_combination -hb_rel
  have hratio : σ (a / b) = M * (a / b) := by
    rw [map_div₀, hshift_a, hshift_b, hscalar]
    field_simp
  have hr0 : a / b = 0 := hobstr hratio
  rw [div_eq_zero_iff] at hr0
  rcases hr0 with h' | h'
  · exact ha h'
  · exact hb h'

end GenericShiftHolder

end GaloisForLFunctions

end
