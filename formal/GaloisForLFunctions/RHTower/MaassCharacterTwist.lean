import GaloisForLFunctions.RHTower.HalfWeightTwistedTheta
import GaloisForLFunctions.RHTower.HalfWeightShimuraKernel

/-!
# Twists of Maass cusp forms by Dirichlet characters

For a Maass cusp eigenform `u` on `Γ₀(N+1)` and a Dirichlet character `χ` mod `q`:

* `maass_translate`: for `γ ∈ Γ₀((N+1)q²)`, `u(γz + a/q) = u(z + ad²/q)`. The matrix
  `[[1, a/q],[0,1]] γ [[1, -ad²/q],[0,1]]` is integral and lies in `Γ₀(N+1)`.
* `uTw`: `u_χ(z) = Σ_{a mod q} χ̄(a) u(z + a/q)`, and **`uTw_smul`**: `u_χ(γz) = χ(d)² u_χ(z)` on
  `Γ₀((N+1)q²)` (reindex `a ↦ ad²`).

This is the weight-0 counterpart of `thetaTw`. The product `u · \overline{u_χ}` transforms under
`Γ₀((N+1)q²)` with the character `χ̄(d)²`, the input of the twisted Rankin–Selberg integral.
-/

open Complex Matrix Filter Topology UpperHalfPlane
open scoped MatrixGroups Real

namespace GaloisForLFunctions.RHTower.HalfWeight

open SelbergMaassFourier SelbergMaassMean SelbergThreeSixteenths
open _root_.RHTower GaloisForLFunctions.RHTower

noncomputable section

section MaassTwist

variable (N : ℕ) {lam : ℝ}
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma0 (N + 1))) lam)

theorem maass_gamma0_inv {g : SL(2, ℤ)} (hg : g ∈ CongruenceSubgroup.Gamma0 (N + 1)) (w : ℍ) :
    f.1.1 (g • w) = f.1.1 w := by
  have hm : integralSL2ToReal g ∈ realImage (CongruenceSubgroup.Gamma0 (N + 1)) := ⟨_, hg, rfl⟩
  have hi := f.1.property ⟨integralSL2ToReal g, hm⟩ w
  rw [integral_action] at hi
  exact hi

/-- The positive case of `maass_translate`. -/
theorem maass_translate_pos {q F : ℕ} (hq0 : q ≠ 0) (hNF : N + 1 ∣ F) {γ : SL(2, ℤ)}
    (hc : ent γ 1 0 = ((q * (q * F) : ℕ) : ℤ)) (a : ℤ) (z : ℍ) :
    (f.1.1 ∘ ofComplex) (((γ • z : ℍ) : ℂ) + (a : ℂ) / q) =
      (f.1.1 ∘ ofComplex) ((z : ℂ) + a * (ent γ 1 1 : ℂ) ^ 2 / q) := by
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq0
  obtain ⟨α, hα⟩ : ∃ α, ent γ 0 0 = α := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, ent γ 0 1 = β := ⟨_, rfl⟩
  obtain ⟨c, hc'⟩ : ∃ c, ent γ 1 0 = c := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, ent γ 1 1 = d := ⟨_, rfl⟩
  have hdet : α * d - β * c = 1 := by rw [← hα, ← hβ, ← hc', ← hd]; exact det_entries γ
  have hcq : c = q * q * F := by rw [← hc', hc]; push_cast; ring
  let γ' : SL(2, ℤ) := ⟨!![α + a * q * F, β - a * d * β * q * F - a ^ 2 * d ^ 2 * F;
      c, d - q * F * a * d ^ 2], by
    rw [Matrix.det_fin_two_of]
    linear_combination (1 - a * q * F * d) * hdet + a ^ 2 * d ^ 2 * F * hcq⟩
  have e10 : ent γ' 1 0 = c := by simp [ent, γ']
  have e11 : ent γ' 1 1 = d - q * F * a * d ^ 2 := by simp [ent, γ']
  have e00 : ent γ' 0 0 = α + a * q * F := by simp [ent, γ']
  have e01 : ent γ' 0 1 = β - a * d * β * q * F - a ^ 2 * d ^ 2 * F := by simp [ent, γ']
  set w : ℍ := ((a * d ^ 2 / q : ℝ)) +ᵥ z with hw
  have hwC : (w : ℂ) = (z : ℂ) + a * (d : ℂ) ^ 2 / q := by
    rw [hw, UpperHalfPlane.coe_vadd]; push_cast; ring
  have hcz : (c : ℂ) * z + d ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero γ z
    rwa [denom_ent, hc', hd] at this
  have hcqC : (c : ℂ) = q * q * F := by exact_mod_cast hcq
  have hcw : (c : ℂ) * w + ((d - q * F * a * d ^ 2 : ℤ) : ℂ) = (c : ℂ) * z + d := by
    rw [hwC, hcqC]; push_cast; field_simp; ring
  have hact : ((γ' • w : ℍ) : ℂ) = (γ • z : ℍ) + (a : ℂ) / q := by
    rw [coe_smul_ent, coe_smul_ent, e00, e01, e10, e11, hcw, hα, hβ, hc', hd,
      div_add_div _ _ hcz hqC, div_eq_div_iff hcz (mul_ne_zero hcz hqC)]
    have hdetC : (α : ℂ) * d - β * c = 1 := by exact_mod_cast hdet
    have hwq : (w : ℂ) * q = z * q + a * d ^ 2 := by rw [hwC]; field_simp
    push_cast
    linear_combination ((a : ℂ) * d * ((c : ℂ) * z + d)) * hdetC +
      (-(a : ℂ) * ((z : ℂ) - d * β) * ((c : ℂ) * z + d)) * hcqC +
      (((α : ℂ) + a * q * F) * ((c : ℂ) * z + d)) * hwq
  have hγ' : γ' ∈ CongruenceSubgroup.Gamma0 (N + 1) := by
    rw [CongruenceSubgroup.Gamma0_mem]
    have : ((N + 1 : ℕ) : ℤ) ∣ ent γ' 1 0 := by
      rw [e10, hcq]
      obtain ⟨k, hk⟩ := hNF
      exact ⟨q * q * k, by rw [hk]; push_cast; ring⟩
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 this
  simp only [Function.comp]
  rw [← hact, hd, ← hwC, ofComplex_apply, ofComplex_apply, maass_gamma0_inv N f hγ']

/-- Integer translations. -/
theorem maass_add_int (w : ℂ) (hw : 0 < w.im) (k : ℤ) :
    (f.1.1 ∘ ofComplex) (w + k) = (f.1.1 ∘ ofComplex) w := by
  have hT : ModularGroup.T ^ k ∈ CongruenceSubgroup.Gamma0 (N + 1) := by
    rw [CongruenceSubgroup.Gamma0_mem, ModularGroup.coe_T_zpow]; simp
  have hw' : 0 < (w + k).im := by simpa using hw
  simp only [Function.comp]
  rw [ofComplex_apply_of_im_pos hw', ofComplex_apply_of_im_pos hw]
  have h := maass_gamma0_inv N f hT ⟨w, hw⟩
  rw [UpperHalfPlane.modular_T_zpow_smul] at h
  rw [← h]
  refine congrArg f.1.1 (UpperHalfPlane.ext ?_)
  rw [UpperHalfPlane.coe_vadd]
  simp [add_comm]

/-- **Maass forms translated by `a/q`**: for `γ ∈ Γ₀((N+1)q²)`,
`u(γz + a/q) = u(z + a d²/q)`. The matrix `[[1, a/q],[0,1]] γ [[1, -ad²/q],[0,1]]` lies in
`Γ₀(N+1)`. -/
theorem maass_translate {q : ℕ} (hq0 : q ≠ 0) {γ : SL(2, ℤ)}
    (hγ : (((N + 1) * q ^ 2 : ℕ) : ℤ) ∣ ent γ 1 0) (a : ℤ) (z : ℍ) :
    (f.1.1 ∘ ofComplex) (((γ • z : ℍ) : ℂ) + (a : ℂ) / q) =
      (f.1.1 ∘ ofComplex) ((z : ℂ) + a * (ent γ 1 1 : ℂ) ^ 2 / q) := by
  obtain ⟨t, ht⟩ := hγ
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq0
  rcases lt_trichotomy t 0 with h | h | h
  · have hn : ent (-γ) 1 0 = ((q * (q * ((N + 1) * (-t).toNat)) : ℕ) : ℤ) := by
      rw [ent_neg, ht]; push_cast; rw [Int.toNat_of_nonneg (by omega)]; ring
    have := maass_translate_pos N f hq0 (dvd_mul_right _ _) hn a z
    rwa [ModularGroup.SL_neg_smul, ent_neg, Int.cast_neg, neg_sq] at this
  · subst h
    have hc : ent γ 1 0 = 0 := by rw [ht]; ring
    have hdet := det_entries γ
    rw [hc, mul_zero, sub_zero] at hdet
    have hzq : 0 < ((z : ℂ) + (a : ℂ) / q).im := by
      have : ((a : ℂ) / q).im = 0 := by
        rw [show (a : ℂ) / q = (((a : ℝ) / q : ℝ) : ℂ) by push_cast; ring]; exact Complex.ofReal_im _
      rw [Complex.add_im, this, add_zero]; exact z.im_pos
    rw [coe_smul_ent, hc]
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨ha, hd⟩ | ⟨ha, hd⟩
    · rw [ha, hd]
      have : ((1 : ℤ) * (z : ℂ) + ent γ 0 1) / (((0 : ℤ) : ℂ) * z + ((1 : ℤ) : ℂ)) + (a : ℂ) / q =
          ((z : ℂ) + (a : ℂ) / q) + (ent γ 0 1 : ℤ) := by push_cast; ring
      rw [this, maass_add_int N f _ hzq]
      congr 1; push_cast; ring
    · rw [ha, hd]
      have : (((-1 : ℤ) : ℂ) * (z : ℂ) + ent γ 0 1) / (((0 : ℤ) : ℂ) * z + ((-1 : ℤ) : ℂ)) +
          (a : ℂ) / q = ((z : ℂ) + (a : ℂ) / q) + ((-ent γ 0 1 : ℤ) : ℂ) := by
        push_cast; field_simp; ring
      rw [this, maass_add_int N f _ hzq]
      congr 1; push_cast; ring
  · have hn : ent γ 1 0 = ((q * (q * ((N + 1) * t.toNat)) : ℕ) : ℤ) := by
      rw [ht]; push_cast; rw [Int.toNat_of_nonneg (by omega)]; ring
    exact maass_translate_pos N f hq0 (dvd_mul_right _ _) hn a z

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

theorem im_add_real_div (w : ℂ) (r : ℝ) : (w + (r : ℂ)).im = w.im := by simp

theorem maass_add_val {w : ℂ} (hw : 0 < w.im) (x : ℤ) :
    (f.1.1 ∘ ofComplex) (w + ((((x : ZMod q)).val : ℕ) : ℂ) / q) =
      (f.1.1 ∘ ofComplex) (w + (x : ℂ) / q) := by
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne q)
  have hv : ((((x : ZMod q)).val : ℕ) : ℤ) = x - q * (x / q) := by
    rw [ZMod.val_intCast, Int.emod_def]
  have hv' : ((((x : ZMod q)).val : ℕ) : ℂ) = (x : ℂ) - q * ((x / q : ℤ) : ℂ) := by exact_mod_cast hv
  have e : w + ((((x : ZMod q)).val : ℕ) : ℂ) / q = (w + (x : ℂ) / q) + ((-(x / q) : ℤ) : ℂ) := by
    rw [hv']; push_cast; field_simp; ring
  have hwx : 0 < (w + (x : ℂ) / q).im := by
    rw [show (x : ℂ) / q = (((x : ℝ) / q : ℝ) : ℂ) by push_cast; ring, im_add_real_div]; exact hw
  rw [e, maass_add_int N f _ hwx]

/-- **The twist of a Maass form** `u_χ(z) = Σ_{a mod q} χ̄(a) u(z + a/q)`. -/
def uTw (z : ℂ) : ℂ := ∑ a : ZMod q, starRingEnd ℂ (χ a) * (f.1.1 ∘ ofComplex) (z + ((a.val : ℕ) : ℂ) / q)

/-- **The transformation law of `u_χ`**: for `γ ∈ Γ₀((N+1)q²)`, `u_χ(γz) = χ(d)² u_χ(z)`. -/
theorem uTw_smul {γ : SL(2, ℤ)} (hγ : (((N + 1) * q ^ 2 : ℕ) : ℤ) ∣ ent γ 1 0) (z : ℍ) :
    uTw N f χ ((γ • z : ℍ) : ℂ) = χ ((ent γ 1 1 : ℤ) : ZMod q) ^ 2 * uTw N f χ z := by
  have hq0 : q ≠ 0 := NeZero.ne q
  have hqd : (q : ℤ) ∣ ent γ 1 0 := by
    refine dvd_trans ?_ hγ
    push_cast
    exact ⟨(N + 1) * q, by ring⟩
  have hdu : IsUnit ((ent γ 1 1 : ℤ) : ZMod q) := by
    obtain ⟨u', v', huv⟩ := isCoprime_d_of_dvd hqd
    have h1 : ((ent γ 1 1 : ℤ) : ZMod q) * ((u' : ℤ) : ZMod q) = 1 := by
      have := congrArg (fun t : ℤ => (t : ZMod q)) huv
      push_cast at this
      rw [ZMod.natCast_self, mul_zero, add_zero] at this
      rw [mul_comm]; exact this
    exact IsUnit.of_mul_eq_one _ h1
  obtain ⟨u, hu⟩ := hdu
  unfold uTw
  have step : ∀ a : ZMod q, starRingEnd ℂ (χ a) *
      (f.1.1 ∘ ofComplex) (((γ • z : ℍ) : ℂ) + ((a.val : ℕ) : ℂ) / q) =
      starRingEnd ℂ (χ a) * (f.1.1 ∘ ofComplex) ((z : ℂ) + (((a * (u : ZMod q) ^ 2).val : ℕ) : ℂ) / q) := by
    intro a
    have h := maass_translate N f hq0 hγ (a.val : ℤ) z
    push_cast at h
    rw [h]
    have hx : ((((a.val : ℤ) * ent γ 1 1 ^ 2 : ℤ) : ZMod q)) = a * (u : ZMod q) ^ 2 := by
      push_cast; rw [hu]; simp
    have := maass_add_val N f (q := q) z.im_pos ((a.val : ℤ) * ent γ 1 1 ^ 2)
    rw [hx] at this
    rw [this]; push_cast; ring_nf
  simp_rw [step]
  have hre : ∑ a : ZMod q, starRingEnd ℂ (χ a) *
      (f.1.1 ∘ ofComplex) ((z : ℂ) + (((a * (u : ZMod q) ^ 2).val : ℕ) : ℂ) / q) =
      χ (u : ZMod q) ^ 2 * ∑ b : ZMod q, starRingEnd ℂ (χ b) *
        (f.1.1 ∘ ofComplex) ((z : ℂ) + ((b.val : ℕ) : ℂ) / q) := by
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Units.mulRight (u ^ 2)) _ _ fun a => ?_
    simp only [Units.mulRight_apply, Units.val_pow_eq_pow_val]
    have : a = (a * (u : ZMod q) ^ 2) * ((u⁻¹ : (ZMod q)ˣ) : ZMod q) ^ 2 := by
      rw [mul_assoc, ← mul_pow, Units.mul_inv, one_pow, mul_one]
    have hψ : starRingEnd ℂ (χ a) = starRingEnd ℂ (χ (a * (u : ZMod q) ^ 2)) * χ (u : ZMod q) ^ 2 := by
      conv_lhs => rw [this]
      rw [map_mul, map_pow, map_mul, map_pow, conj_char_units_inv]
    rw [hψ]
    ring
  rw [hre, hu]

end MaassTwist

end

end GaloisForLFunctions.RHTower.HalfWeight
