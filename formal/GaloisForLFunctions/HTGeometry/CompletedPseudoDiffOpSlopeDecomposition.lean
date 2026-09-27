import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpRelativeSplitting

/-!
# The rational slope decomposition of a semilinear automorphism

Let `T` be a uniformizer-semilinear automorphism of a finite-dimensional completed skew vector space
`E`.  For a rational number `s = c/d` the normalized power `S_s = ϖ^c T^d` has a neutral part
`N(S_s) = B(S_s) ⊓ B(S_s⁻¹)`: the vectors on which `T^d` acts, up to bounded error, as `ϖ^{-c}`.
This is the **slope-`s` part** `DiffOp.slopeSubspace T hT s`; it carries a lattice fixed by `S_s`.

* `DiffOp.iSup_slopeSubspace_eq_top` — **the slope parts span `E`.**  Strong induction on the
  dimension of a `T`-stable subspace `W`: with `d = dim W` and `c = deg_T W`, the normalized power
  `S = ϖ^c T^d` has degree `0` on `W`; `W` splits into the pieces of `S`, whose degrees are positive,
  zero and negative, so either `W` is neutral for `S` (hence inside the slope-`c/d` part) or both
  extreme pieces are proper and the induction applies to them.
* `DiffOp.iSupIndep_slopeSubspace` — the slope parts are independent: for `t < s` the slope-`t` part is
  forward contracted by `S_s`, for `t > s` backward contracted, and the neutral part of `S_s` meets
  neither contracting part.
* `DiffOp.forwardBoundedSubspace_slopeAut_eq` and `DiffOp.backwardContractingSubspace_slopeAut_eq` —
  the two opposite flags: `B(S_s) = ⨁_{t ≤ s} E_t` and `C(S_s) = ⨁_{t > s} E_t`.
-/

open Filter

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type*} [Field K] [Differential K]

attribute [local instance] completedPseudoDiffOpIntegerSMul

variable {E : Type*} [AddCommGroup E] [Module (CompletedPseudoDiffOp K) E]

variable {T : E ≃ₗ[ℤ] E} (hT : IsUniformizerSemilinear (K := K) T)

theorem uniformizerSMulAut_mul (a b : ℤ) :
    uniformizerSMulAut (K := K) (E := E) a * uniformizerSMulAut (K := K) (E := E) b =
      uniformizerSMulAut (K := K) (E := E) (a + b) := by
  ext x
  rw [LinearEquiv.mul_apply, uniformizerSMulAut_apply, uniformizerSMulAut_apply,
    uniformizerSMulAut_apply, smul_smul, ← uniformizerZPow_add]

theorem uniformizerSMulAut_pow (a : ℤ) (k : ℕ) :
    uniformizerSMulAut (K := K) (E := E) a ^ k = uniformizerSMulAut (K := K) (E := E) (k * a) := by
  induction k with
  | zero =>
      ext x
      rw [pow_zero, LinearEquiv.coe_one, id, Nat.cast_zero, zero_mul, uniformizerSMulAut_apply,
        uniformizerZPow_zero, one_smul]
  | succ k ih =>
      rw [pow_succ, ih, uniformizerSMulAut_mul]
      congr 1
      push_cast
      ring

include hT in
theorem commute_uniformizerSMulAut (a : ℤ) : Commute T (uniformizerSMulAut (K := K) a) := by
  ext x
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, uniformizerSMulAut_apply,
    uniformizerSMulAut_apply, IsUniformizerSemilinear.map_uniformizerZPow_smul hT]

/-- The normalized power `ϖ^c T^d`. -/
def slopeAut (T : E ≃ₗ[ℤ] E) (c : ℤ) (d : ℕ) : E ≃ₗ[ℤ] E :=
  uniformizerSMulAut (K := K) c * T ^ d

include hT in
theorem isUniformizerSemilinear_slopeAut (c : ℤ) (d : ℕ) :
    IsUniformizerSemilinear (K := K) (slopeAut (K := K) T c d) :=
  (isUniformizerSemilinear_uniformizerSMulAut c).mul (hT.pow d)

include hT in
theorem commute_slopeAut (c : ℤ) (d : ℕ) : Commute T (slopeAut (K := K) T c d) :=
  (commute_uniformizerSMulAut hT c).mul_right ((Commute.refl T).pow_right d)

include hT in
theorem slopeAut_pow (c : ℤ) (d k : ℕ) :
    slopeAut (K := K) T c d ^ k = slopeAut (K := K) T (k * c) (k * d) := by
  rw [slopeAut, slopeAut, ((commute_uniformizerSMulAut hT c).symm.pow_right d).mul_pow,
    uniformizerSMulAut_pow, ← pow_mul, mul_comm d k]

/-- A reduced fraction divides every representation of the same rational number. -/
theorem exists_eq_mul_num_den (c : ℤ) {d : ℕ} (hd : 1 ≤ d) (q : ℚ) (hq : q * d = c) :
    ∃ k : ℕ, 1 ≤ k ∧ c = k * q.num ∧ d = k * q.den := by
  have hcross : c * (q.den : ℤ) = q.num * d := by
    have h := Rat.mul_den_eq_num q
    have : (c : ℚ) * q.den = q.num * d := by
      rw [← h, ← hq]
      ring
    exact_mod_cast this
  have hcop : IsCoprime (q.den : ℤ) q.num := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
    exact q.reduced
  have hdvd : (q.den : ℤ) ∣ d := hcop.dvd_of_dvd_mul_left ⟨c, by rw [mul_comm]; linarith⟩
  obtain ⟨k, hk⟩ := hdvd
  have hden : 0 < (q.den : ℤ) := by exact_mod_cast q.den_pos
  have hkpos : 0 < k := by
    have : (0 : ℤ) < d := by exact_mod_cast (show 0 < d by omega)
    nlinarith
  refine ⟨k.toNat, by omega, ?_, ?_⟩
  · have : c * (q.den : ℤ) = (q.num * k) * q.den := by rw [hcross, hk]; ring
    have hc : c = q.num * k := mul_right_cancel₀ (ne_of_gt hden) this
    rw [hc, Int.toNat_of_nonneg hkpos.le]
    ring
  · have : (d : ℤ) = k.toNat * q.den := by rw [hk, Int.toNat_of_nonneg hkpos.le]; ring
    exact_mod_cast this

section Slopes

/-- The slope-`s` part: the neutral part of `ϖ^{num s} T^{den s}`. -/
def slopeSubspace (T : E ≃ₗ[ℤ] E) (hT : IsUniformizerSemilinear (K := K) T) (s : ℚ) :
    Submodule (CompletedPseudoDiffOp K) E :=
  forwardBoundedSubspace (slopeAut (K := K) T s.num s.den)
      (isUniformizerSemilinear_slopeAut hT s.num s.den) ⊓
    forwardBoundedSubspace (slopeAut (K := K) T s.num s.den)⁻¹
      (isUniformizerSemilinear_slopeAut hT s.num s.den).inv


/-- The neutral part of `ϖ^c T^d` is the slope-`c/d` part. -/
theorem neutral_slopeAut_eq_slopeSubspace (c : ℤ) {d : ℕ} (hd : 1 ≤ d) :
    forwardBoundedSubspace (slopeAut (K := K) T c d) (isUniformizerSemilinear_slopeAut hT c d) ⊓
      forwardBoundedSubspace (slopeAut (K := K) T c d)⁻¹
        (isUniformizerSemilinear_slopeAut hT c d).inv =
      slopeSubspace T hT ((c : ℚ) / d) := by
  have hq : ((c : ℚ) / d) * d = c := by
    have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
    field_simp
  obtain ⟨k, hk, hc, hdk⟩ := exists_eq_mul_num_den c hd _ hq
  set q : ℚ := (c : ℚ) / d
  have hpow : slopeAut (K := K) T c d = slopeAut (K := K) T q.num q.den ^ k := by
    rw [slopeAut_pow hT, ← hc, ← hdk]
  have hS := isUniformizerSemilinear_slopeAut hT q.num q.den
  rw [slopeSubspace, forwardBoundedSubspace_congr hpow _ (hS.pow k),
    forwardBoundedSubspace_congr (show (slopeAut (K := K) T c d)⁻¹ =
      (slopeAut (K := K) T q.num q.den)⁻¹ ^ k by rw [hpow, inv_pow]) _ (hS.inv.pow k),
    forwardBoundedSubspace_pow hS hk, forwardBoundedSubspace_pow hS.inv hk]

theorem uniformizerSMulAut_inv (a : ℤ) :
    (uniformizerSMulAut (K := K) (E := E) a)⁻¹ = uniformizerSMulAut (K := K) (E := E) (-a) := by
  ext x
  rfl

include hT in
theorem slopeAut_inv (c : ℤ) (d : ℕ) :
    (slopeAut (K := K) T c d)⁻¹ = slopeAut (K := K) T⁻¹ (-c) d := by
  rw [slopeAut, slopeAut, mul_inv_rev, uniformizerSMulAut_inv, ← inv_pow]
  exact (((commute_uniformizerSMulAut hT (-c)).inv_left).pow_left d).eq

include hT in
/-- Two normalized powers compare by a uniformizer power. -/
theorem slopeAut_pow_eq_uniformizerSMulAut_mul (c c' : ℤ) (d d' : ℕ) :
    slopeAut (K := K) T c d ^ d' =
      uniformizerSMulAut (K := K) (c * d' - c' * d) * slopeAut (K := K) T c' d' ^ d := by
  rw [slopeAut_pow hT, slopeAut_pow hT, slopeAut, slopeAut, ← mul_assoc, uniformizerSMulAut_mul]
  congr 2
  · ring
  · ring

/-- If `S^k = ϖ^e R` with `e ≥ 1` and `x` is forward bounded for `R`, then `S` contracts `x`
forward. -/
theorem mem_backwardContractingSubspace_inv_of_pow_eq {S R : E ≃ₗ[ℤ] E}
    (hS : IsUniformizerSemilinear (K := K) S) (hR : IsUniformizerSemilinear (K := K) R)
    {k : ℕ} (hk : 1 ≤ k) {e : ℤ} (he : 1 ≤ e)
    (hSR : S ^ k = uniformizerSMulAut (K := K) e * R) {x : E}
    (hx : x ∈ forwardBoundedSubspace R hR) : x ∈ backwardContractingSubspace S⁻¹ hS.inv := by
  rw [← backwardContractingSubspace_pow hS.inv hk]
  obtain ⟨M, hM, hMx⟩ := mem_forwardBoundedSubspace.1 hx
  refine mem_backwardContractingSubspace.2 ⟨M, hM, fun j => eventually_atTop.2 ⟨j, fun n hn => ?_⟩⟩
  have hcomm : Commute (uniformizerSMulAut (K := K) (E := E) e) R :=
    (commute_uniformizerSMulAut hR e).symm
  have hpow : ((S⁻¹ ^ k)⁻¹ ^ n) x = uniformizerZPow (K := K) (n * e) • (R ^ n) x := by
    rw [show (S⁻¹ ^ k)⁻¹ = S ^ k by rw [inv_pow, inv_inv], hSR, hcomm.mul_pow,
      uniformizerSMulAut_pow, LinearEquiv.mul_apply, uniformizerSMulAut_apply]
  rw [hpow]
  refine uniformizerDilate_antitone M ?_ (smul_mem_uniformizerDilate _ (hMx n))
  have : (j : ℤ) ≤ n := by exact_mod_cast hn
  nlinarith

theorem num_mul_den_lt_of_lt {t s : ℚ} (h : t < s) : t.num * s.den < s.num * t.den := by
  have ht : (0 : ℚ) < t.den := by exact_mod_cast t.den_pos
  have hs : (0 : ℚ) < s.den := by exact_mod_cast s.den_pos
  have h' : (t.num : ℚ) / t.den < s.num / s.den := by rwa [Rat.num_div_den, Rat.num_div_den]
  rw [div_lt_div_iff₀ ht hs] at h'
  exact_mod_cast h'

/-- For `t < s` the slope-`t` part is forward contracted by `S_s`. -/
theorem slopeSubspace_le_backwardContractingSubspace_inv {s t : ℚ} (hts : t < s) :
    slopeSubspace T hT t ≤ backwardContractingSubspace (slopeAut (K := K) T s.num s.den)⁻¹
      (isUniformizerSemilinear_slopeAut hT s.num s.den).inv := by
  intro x hx
  have hSt := isUniformizerSemilinear_slopeAut hT t.num t.den
  have hxb : x ∈ forwardBoundedSubspace (slopeAut (K := K) T t.num t.den ^ s.den)
      (hSt.pow s.den) := by
    rw [forwardBoundedSubspace_pow hSt s.den_pos]
    exact hx.1
  have he : 1 ≤ s.num * (t.den : ℤ) - t.num * s.den := by
    have := num_mul_den_lt_of_lt hts
    omega
  exact mem_backwardContractingSubspace_inv_of_pow_eq
    (isUniformizerSemilinear_slopeAut hT s.num s.den) (hSt.pow s.den) t.den_pos he
    (slopeAut_pow_eq_uniformizerSMulAut_mul hT s.num t.num s.den t.den) hxb

/-- For `t > s` the slope-`t` part is backward contracted by `S_s`. -/
theorem slopeSubspace_le_backwardContractingSubspace {s t : ℚ} (hst : s < t) :
    slopeSubspace T hT t ≤ backwardContractingSubspace (slopeAut (K := K) T s.num s.den)
      (isUniformizerSemilinear_slopeAut hT s.num s.den) := by
  intro x hx
  have hSt := isUniformizerSemilinear_slopeAut hT.inv (-t.num) t.den
  have hSs := isUniformizerSemilinear_slopeAut hT.inv (-s.num) s.den
  have hxb : x ∈ forwardBoundedSubspace (slopeAut (K := K) T⁻¹ (-t.num) t.den ^ s.den)
      (hSt.pow s.den) := by
    rw [forwardBoundedSubspace_pow hSt s.den_pos,
      forwardBoundedSubspace_congr (slopeAut_inv hT t.num t.den).symm hSt
        (isUniformizerSemilinear_slopeAut hT t.num t.den).inv]
    exact hx.2
  have he : 1 ≤ -s.num * (t.den : ℤ) - -t.num * s.den := by
    have := num_mul_den_lt_of_lt hst
    have h2 : -s.num * (t.den : ℤ) - -t.num * s.den = t.num * s.den - s.num * t.den := by ring
    rw [h2]
    omega
  have h := mem_backwardContractingSubspace_inv_of_pow_eq hSs (hSt.pow s.den) t.den_pos he
    (slopeAut_pow_eq_uniformizerSMulAut_mul hT.inv (-s.num) (-t.num) s.den t.den) hxb
  rwa [backwardContractingSubspace_congr (show (slopeAut (K := K) T⁻¹ (-s.num) s.den)⁻¹ =
    slopeAut (K := K) T s.num s.den by rw [← slopeAut_inv hT, inv_inv]) hSs.inv
    (isUniformizerSemilinear_slopeAut hT s.num s.den)] at h

variable [FiniteDimensional (CompletedPseudoDiffOp K) E]

/-- The degree of a power. -/
theorem semilinearDegree_pow' {S : E ≃ₗ[ℤ] E} (hS : IsUniformizerSemilinear (K := K) S)
    {W : Submodule (CompletedPseudoDiffOp K) E} (hW : ∀ x ∈ W, S x ∈ W)
    (hW' : ∀ x ∈ W, S⁻¹ x ∈ W) (n : ℕ) :
    semilinearDegree (S ^ n) (hS.pow n) W = n * semilinearDegree S hS W := by
  induction n with
  | zero =>
      rw [semilinearDegree_congr (pow_zero S) (hS.pow 0) IsUniformizerSemilinear.one W,
        semilinearDegree_one]
      simp
  | succ n ih =>
      rw [semilinearDegree_congr (pow_succ S n) (hS.pow (n + 1)) ((hS.pow n).mul hS) W,
        semilinearDegree_mul (hS.pow n) hS (pow_apply_mem_of_forall hW n)
          (fun x hx => by rw [← inv_pow]; exact pow_apply_mem_of_forall hW' n x hx) hW hW', ih]
      push_cast
      ring

omit [FiniteDimensional (CompletedPseudoDiffOp K) E] in
/-- Every automorphism commuting with `S` preserves the four pieces of `S`. -/
theorem pieces_invariant_of_commute {S R : E ≃ₗ[ℤ] E} (hS : IsUniformizerSemilinear (K := K) S)
    (hR : IsUniformizerSemilinear (K := K) R) (hc : Commute R S) :
    (∀ x ∈ forwardBoundedSubspace S hS, R x ∈ forwardBoundedSubspace S hS) ∧
      (∀ x ∈ backwardContractingSubspace S hS, R x ∈ backwardContractingSubspace S hS) ∧
      (∀ x ∈ forwardBoundedSubspace S⁻¹ hS.inv, R x ∈ forwardBoundedSubspace S⁻¹ hS.inv) ∧
      (∀ x ∈ backwardContractingSubspace S⁻¹ hS.inv,
        R x ∈ backwardContractingSubspace S⁻¹ hS.inv) :=
  ⟨fun _ hx => apply_mem_forwardBoundedSubspace_of_commute hS hR hc hx,
    fun _ hx => apply_mem_backwardContractingSubspace_of_commute hS hR hc hx,
    fun _ hx => apply_mem_forwardBoundedSubspace_of_commute hS.inv hR hc.inv_right hx,
    fun _ hx => apply_mem_backwardContractingSubspace_of_commute hS.inv hR hc.inv_right hx⟩

/-- **The slope parts span every stable subspace.** -/
theorem le_iSup_slopeSubspace : ∀ (n : ℕ) (W : Submodule (CompletedPseudoDiffOp K) E),
    Module.finrank (CompletedPseudoDiffOp K) W = n → (∀ x ∈ W, T x ∈ W) →
      (∀ x ∈ W, T⁻¹ x ∈ W) → W ≤ ⨆ s : ℚ, slopeSubspace T hT s := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W hWn hW hW'
  by_cases hW0 : W = ⊥
  · rw [hW0]
    exact bot_le
  have hn : 1 ≤ n := by
    have := (Module.finrank_pos_iff (R := CompletedPseudoDiffOp K) (M := W)).2
      (Submodule.nontrivial_iff_ne_bot.2 hW0)
    omega
  obtain ⟨c, hc⟩ : ∃ c : ℤ, c = semilinearDegree T hT W := ⟨_, rfl⟩
  have hS := isUniformizerSemilinear_slopeAut hT c n
  have hSW : ∀ x ∈ W, slopeAut (K := K) T c n x ∈ W := fun x hx => by
    rw [slopeAut, LinearEquiv.mul_apply, uniformizerSMulAut_apply]
    exact W.smul_mem _ (pow_apply_mem_of_forall hW n x hx)
  have hSW' : ∀ x ∈ W, (slopeAut (K := K) T c n)⁻¹ x ∈ W := fun x hx => by
    rw [slopeAut_inv hT, slopeAut, LinearEquiv.mul_apply, uniformizerSMulAut_apply]
    exact W.smul_mem _ (pow_apply_mem_of_forall hW' n x hx)
  have hdeg : semilinearDegree (slopeAut (K := K) T c n) hS W = 0 := by
    rw [semilinearDegree_congr (show slopeAut (K := K) T c n =
        uniformizerSMulAut (K := K) c * T ^ n from rfl) hS
        ((isUniformizerSemilinear_uniformizerSMulAut c).mul (hT.pow n)) W,
      semilinearDegree_mul (isUniformizerSemilinear_uniformizerSMulAut c) (hT.pow n)
        (fun x hx => W.smul_mem _ hx) (fun x hx => W.smul_mem _ hx)
        (pow_apply_mem_of_forall hW n)
        (fun x hx => by rw [← inv_pow]; exact pow_apply_mem_of_forall hW' n x hx),
      semilinearDegree_uniformizerSMulAut, semilinearDegree_pow' hT hW hW' n, hWn, ← hc]
    ring
  -- the pieces of `S = ϖ^c Tⁿ`
  obtain ⟨hTB, hTC, hTB', hTC'⟩ := pieces_invariant_of_commute hS hT (commute_slopeAut hT c n)
  obtain ⟨hTiB, hTiC, hTiB', hTiC'⟩ := pieces_invariant_of_commute hS hT.inv
    (commute_slopeAut hT c n).inv_left
  obtain ⟨hSB, hSC, hSB', hSC'⟩ := pieces_invariant_of_commute hS hS (Commute.refl _)
  obtain ⟨hSiB, hSiC, hSiB', hSiC'⟩ := pieces_invariant_of_commute hS hS.inv
    (Commute.refl _).inv_left
  set S := slopeAut (K := K) T c n with hSdef
  set Wp := W ⊓ backwardContractingSubspace S hS with hWp
  set W0 := W ⊓ (forwardBoundedSubspace S hS ⊓ forwardBoundedSubspace S⁻¹ hS.inv) with hW0def
  set Wm := W ⊓ backwardContractingSubspace S⁻¹ hS.inv with hWm
  have hsplit : W = Wp ⊔ (W0 ⊔ Wm) := by
    rw [hW0def, hWm, inf_neutral_sup_inf_eq_of_invariant hS hSW hSW', hWp, sup_comm,
      inf_sup_inf_eq_of_invariant hS hSW hSW']
  -- stability of the pieces
  have stab : ∀ {X : Submodule (CompletedPseudoDiffOp K) E} (R : E ≃ₗ[ℤ] E),
      (∀ x ∈ W, R x ∈ W) → (∀ x ∈ X, R x ∈ X) → ∀ x ∈ W ⊓ X, R x ∈ W ⊓ X :=
    fun R h1 h2 x hx => ⟨h1 x hx.1, h2 x hx.2⟩
  have hSWp : ∀ x ∈ Wp, S x ∈ Wp := stab S hSW hSC
  have hSWp' : ∀ x ∈ Wp, S⁻¹ x ∈ Wp := stab S⁻¹ hSW' hSiC
  have hSW0 : ∀ x ∈ W0, S x ∈ W0 := stab S hSW fun x hx => ⟨hSB x hx.1, hSB' x hx.2⟩
  have hSW0' : ∀ x ∈ W0, S⁻¹ x ∈ W0 := stab S⁻¹ hSW' fun x hx => ⟨hSiB x hx.1, hSiB' x hx.2⟩
  have hSWm : ∀ x ∈ Wm, S x ∈ Wm := stab S hSW hSC'
  have hSWm' : ∀ x ∈ Wm, S⁻¹ x ∈ Wm := stab S⁻¹ hSW' hSiC'
  have hsupinv : ∀ {X Y : Submodule (CompletedPseudoDiffOp K) E} (R : E ≃ₗ[ℤ] E),
      (∀ x ∈ X, R x ∈ X) → (∀ x ∈ Y, R x ∈ Y) → ∀ x ∈ X ⊔ Y, R x ∈ X ⊔ Y := by
    intro X Y R hX hY x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [_root_.map_add]
    exact Submodule.add_mem_sup (hX y hy) (hY z hz)
  -- disjointness
  have hBC := backwardContractingSubspace_inf_forwardBoundedSubspace_eq_bot hS
  have hCB : backwardContractingSubspace S⁻¹ hS.inv ≤ forwardBoundedSubspace S hS :=
    backwardContractingSubspace_inv_le_forwardBoundedSubspace hS
  have hdisj1 : Wp ⊓ (W0 ⊔ Wm) = ⊥ := by
    rw [eq_bot_iff, ← hBC]
    refine inf_le_inf inf_le_right (sup_le ?_ ?_)
    · exact inf_le_right.trans inf_le_left
    · exact inf_le_right.trans hCB
  have hdisj2 : W0 ⊓ Wm = ⊥ := by
    rw [eq_bot_iff, ← neutral_inf_backwardContractingSubspace_inv_eq_bot hS]
    exact inf_le_inf inf_le_right inf_le_right
  have hsum : semilinearDegree S hS W = semilinearDegree S hS Wp +
      (semilinearDegree S hS W0 + semilinearDegree S hS Wm) := by
    conv_lhs => rw [hsplit]
    rw [semilinearDegree_sup hS hdisj1 hSWp hSWp' (hsupinv S hSW0 hSWm) (hsupinv S⁻¹ hSW0' hSWm'),
      semilinearDegree_sup hS hdisj2 hSW0 hSW0' hSWm hSWm']
  have hdeg0 : semilinearDegree S hS W0 = 0 :=
    semilinearDegree_eq_zero_of_le_neutral hS hSW0 hSW0' inf_le_right
  have hpos : Wp ≠ ⊥ → 0 < semilinearDegree S hS Wp := fun h =>
    semilinearDegree_pos_of_le_backwardContracting hS hSWp hSWp' inf_le_right h
  have hneg : Wm ≠ ⊥ → semilinearDegree S hS Wm < 0 := fun h =>
    semilinearDegree_neg_of_le_backwardContracting_inv hS hSWm hSWm' inf_le_right h
  have hbot : semilinearDegree S hS (⊥ : Submodule (CompletedPseudoDiffOp K) E) = 0 :=
    semilinearDegree_eq_zero_of_le_neutral hS (fun x hx => by
      rw [Submodule.mem_bot] at hx ⊢; rw [hx, _root_.map_zero])
      (fun x hx => by rw [Submodule.mem_bot] at hx ⊢; rw [hx, _root_.map_zero]) bot_le
  -- the extreme pieces are proper
  have hWplt : Wp < W := by
    refine lt_of_le_of_ne inf_le_left fun heq => ?_
    have hWm0 : Wm = ⊥ := by
      rw [eq_bot_iff, ← hBC]
      intro x hx
      exact ⟨(heq ▸ hx.1 : x ∈ Wp).2, hCB hx.2⟩
    have hWp0 : Wp ≠ ⊥ := by rw [heq]; exact hW0
    have hp := hpos hWp0
    have h1 := hsum
    rw [hdeg, hdeg0, hWm0, hbot] at h1
    linarith
  have hWmlt : Wm < W := by
    refine lt_of_le_of_ne inf_le_left fun heq => ?_
    have hWp0 : Wp = ⊥ := by
      rw [eq_bot_iff, ← hBC]
      intro x hx
      exact ⟨hx.2, hCB (heq ▸ hx.1 : x ∈ Wm).2⟩
    have hWm0 : Wm ≠ ⊥ := by rw [heq]; exact hW0
    have hm := hneg hWm0
    have h1 := hsum
    rw [hdeg, hdeg0, hWp0, hbot] at h1
    linarith
  have hTWp : ∀ x ∈ Wp, T x ∈ Wp := stab T hW hTC
  have hTWp' : ∀ x ∈ Wp, T⁻¹ x ∈ Wp := stab T⁻¹ hW' hTiC
  have hTWm : ∀ x ∈ Wm, T x ∈ Wm := stab T hW hTC'
  have hTWm' : ∀ x ∈ Wm, T⁻¹ x ∈ Wm := stab T⁻¹ hW' hTiC'
  have hIp := ih _ (hWn ▸ Submodule.finrank_lt_finrank_of_lt hWplt) Wp rfl hTWp hTWp'
  have hIm := ih _ (hWn ▸ Submodule.finrank_lt_finrank_of_lt hWmlt) Wm rfl hTWm hTWm'
  have hI0 : W0 ≤ ⨆ s : ℚ, slopeSubspace T hT s := by
    refine inf_le_right.trans (le_trans (le_of_eq ?_) (le_iSup _ ((c : ℚ) / n)))
    exact neutral_slopeAut_eq_slopeSubspace hT c hn
  rw [hsplit]
  exact sup_le hIp (sup_le hI0 hIm)

/-- **The slope parts span.** -/
theorem iSup_slopeSubspace_eq_top : ⨆ s : ℚ, slopeSubspace T hT s = ⊤ :=
  top_unique (le_iSup_slopeSubspace hT _ ⊤ rfl (fun _ _ => trivial) (fun _ _ => trivial))


/-- **The slope parts are independent.** -/
theorem iSupIndep_slopeSubspace : iSupIndep (slopeSubspace T hT) := by
  intro s
  have hS := isUniformizerSemilinear_slopeAut hT s.num s.den
  have hle : (⨆ t, ⨆ (_ : t ≠ s), slopeSubspace T hT t) ≤
      backwardContractingSubspace (slopeAut (K := K) T s.num s.den) hS ⊔
        backwardContractingSubspace (slopeAut (K := K) T s.num s.den)⁻¹ hS.inv := by
    refine iSup₂_le fun t ht => ?_
    rcases lt_or_gt_of_ne ht with h | h
    · exact (slopeSubspace_le_backwardContractingSubspace_inv hT h).trans le_sup_right
    · exact (slopeSubspace_le_backwardContractingSubspace hT h).trans le_sup_left
  refine Disjoint.mono_right hle ?_
  rw [disjoint_iff, eq_bot_iff]
  rintro x ⟨⟨hxB, hxB'⟩, hx⟩
  obtain ⟨c, hc, m, hm, rfl⟩ := Submodule.mem_sup.1 hx
  have hmB := backwardContractingSubspace_inv_le_forwardBoundedSubspace hS hm
  have hcB : c ∈ forwardBoundedSubspace (slopeAut (K := K) T s.num s.den) hS := by
    have := Submodule.sub_mem _ hxB hmB
    rwa [add_sub_cancel_right] at this
  have hc0 : c = 0 := by
    have h := backwardContractingSubspace_inf_forwardBoundedSubspace_eq_bot hS
    have hmem : c ∈ backwardContractingSubspace (slopeAut (K := K) T s.num s.den) hS ⊓
        forwardBoundedSubspace (slopeAut (K := K) T s.num s.den) hS := ⟨hc, hcB⟩
    rw [h, Submodule.mem_bot] at hmem
    exact hmem
  subst hc0
  rw [zero_add] at hxB' ⊢
  have h := neutral_inf_backwardContractingSubspace_inv_eq_bot hS
  have hmem : m ∈ (forwardBoundedSubspace (slopeAut (K := K) T s.num s.den) hS ⊓
      forwardBoundedSubspace (slopeAut (K := K) T s.num s.den)⁻¹ hS.inv) ⊓
        backwardContractingSubspace (slopeAut (K := K) T s.num s.den)⁻¹ hS.inv :=
    ⟨⟨hmB, hxB'⟩, hm⟩
  rwa [h] at hmem

/-- Only finitely many slopes occur. -/
theorem finite_setOf_slopeSubspace_ne_bot : {s : ℚ | slopeSubspace T hT s ≠ ⊥}.Finite := by
  have := (iSupIndep_slopeSubspace hT).fintypeNeBotOfFiniteDimensional
  exact Set.finite_coe_iff.1 (@Finite.of_fintype _ this)

/-- **The attracting flag.**  `B(S_s)` is the sum of the slope parts of slope at most `s`. -/
theorem forwardBoundedSubspace_slopeAut_eq (s : ℚ) :
    forwardBoundedSubspace (slopeAut (K := K) T s.num s.den)
        (isUniformizerSemilinear_slopeAut hT s.num s.den) =
      ⨆ t, ⨆ (_ : t ≤ s), slopeSubspace T hT t := by
  have hS := isUniformizerSemilinear_slopeAut hT s.num s.den
  have hX : (⨆ t, ⨆ (_ : t ≤ s), slopeSubspace T hT t) ≤
      forwardBoundedSubspace (slopeAut (K := K) T s.num s.den) hS := by
    refine iSup₂_le fun t ht => ?_
    rcases lt_or_eq_of_le ht with h | rfl
    · exact (slopeSubspace_le_backwardContractingSubspace_inv hT h).trans
        (backwardContractingSubspace_inv_le_forwardBoundedSubspace hS)
    · exact inf_le_left
  have hY : (⨆ t, ⨆ (_ : ¬ t ≤ s), slopeSubspace T hT t) ≤
      backwardContractingSubspace (slopeAut (K := K) T s.num s.den) hS :=
    iSup₂_le fun t ht => slopeSubspace_le_backwardContractingSubspace hT (not_le.1 ht)
  refine le_antisymm ?_ hX
  have htop := iSup_slopeSubspace_eq_top hT
  rw [iSup_split _ (fun t => t ≤ s)] at htop
  calc forwardBoundedSubspace (slopeAut (K := K) T s.num s.den) hS
      = forwardBoundedSubspace (slopeAut (K := K) T s.num s.den) hS ⊓
          ((⨆ t, ⨆ (_ : t ≤ s), slopeSubspace T hT t) ⊔
            ⨆ t, ⨆ (_ : ¬ t ≤ s), slopeSubspace T hT t) := by rw [htop, inf_top_eq]
    _ = (⨆ t, ⨆ (_ : t ≤ s), slopeSubspace T hT t) ⊔
          ((⨆ t, ⨆ (_ : ¬ t ≤ s), slopeSubspace T hT t) ⊓
            forwardBoundedSubspace (slopeAut (K := K) T s.num s.den) hS) := by
        rw [inf_comm, sup_inf_assoc_of_le _ hX]
    _ ≤ (⨆ t, ⨆ (_ : t ≤ s), slopeSubspace T hT t) ⊔ ⊥ := by
        refine sup_le_sup_left ?_ _
        rw [← backwardContractingSubspace_inf_forwardBoundedSubspace_eq_bot hS]
        exact inf_le_inf_right _ hY
    _ = ⨆ t, ⨆ (_ : t ≤ s), slopeSubspace T hT t := sup_bot_eq _

/-- **The opposite part.**  `C(S_s)` is the sum of the slope parts of slope larger than `s`. -/
theorem backwardContractingSubspace_slopeAut_eq (s : ℚ) :
    backwardContractingSubspace (slopeAut (K := K) T s.num s.den)
        (isUniformizerSemilinear_slopeAut hT s.num s.den) =
      ⨆ t, ⨆ (_ : s < t), slopeSubspace T hT t := by
  have hS := isUniformizerSemilinear_slopeAut hT s.num s.den
  have hY : (⨆ t, ⨆ (_ : s < t), slopeSubspace T hT t) ≤
      backwardContractingSubspace (slopeAut (K := K) T s.num s.den) hS :=
    iSup₂_le fun t ht => slopeSubspace_le_backwardContractingSubspace hT ht
  have hX : (⨆ t, ⨆ (_ : ¬ s < t), slopeSubspace T hT t) ≤
      forwardBoundedSubspace (slopeAut (K := K) T s.num s.den) hS := by
    rw [forwardBoundedSubspace_slopeAut_eq hT s]
    exact iSup₂_mono' fun t ht => ⟨t, not_lt.1 ht, le_rfl⟩
  refine le_antisymm ?_ hY
  have htop := iSup_slopeSubspace_eq_top hT
  rw [iSup_split _ (fun t => s < t)] at htop
  calc backwardContractingSubspace (slopeAut (K := K) T s.num s.den) hS
      = backwardContractingSubspace (slopeAut (K := K) T s.num s.den) hS ⊓
          ((⨆ t, ⨆ (_ : s < t), slopeSubspace T hT t) ⊔
            ⨆ t, ⨆ (_ : ¬ s < t), slopeSubspace T hT t) := by rw [htop, inf_top_eq]
    _ = (⨆ t, ⨆ (_ : s < t), slopeSubspace T hT t) ⊔
          ((⨆ t, ⨆ (_ : ¬ s < t), slopeSubspace T hT t) ⊓
            backwardContractingSubspace (slopeAut (K := K) T s.num s.den) hS) := by
        rw [inf_comm, sup_inf_assoc_of_le _ hY]
    _ ≤ (⨆ t, ⨆ (_ : s < t), slopeSubspace T hT t) ⊔ ⊥ := by
        refine sup_le_sup_left ?_ _
        rw [← backwardContractingSubspace_inf_forwardBoundedSubspace_eq_bot hS, inf_comm]
        exact inf_le_inf_left _ hX
    _ = ⨆ t, ⨆ (_ : s < t), slopeSubspace T hT t := sup_bot_eq _


/-- **The repelling flag.**  `B(S_s⁻¹)` is the sum of the slope parts of slope at least `s`. -/
theorem forwardBoundedSubspace_inv_slopeAut_eq (s : ℚ) :
    forwardBoundedSubspace (slopeAut (K := K) T s.num s.den)⁻¹
        (isUniformizerSemilinear_slopeAut hT s.num s.den).inv =
      ⨆ t, ⨆ (_ : s ≤ t), slopeSubspace T hT t := by
  have hS := isUniformizerSemilinear_slopeAut hT s.num s.den
  have hB := forwardBoundedSubspace_eq_neutral_sup hS.inv
  have hB' : forwardBoundedSubspace (slopeAut (K := K) T s.num s.den)⁻¹ hS.inv =
      slopeSubspace T hT s ⊔ backwardContractingSubspace (slopeAut (K := K) T s.num s.den) hS := by
    rw [hB, backwardContractingSubspace_congr (inv_inv _) hS.inv.inv hS, slopeSubspace,
      forwardBoundedSubspace_congr (inv_inv _) hS.inv.inv hS, inf_comm]
  rw [hB', backwardContractingSubspace_slopeAut_eq hT s]
  apply le_antisymm
  · refine sup_le (le_iSup₂_of_le s le_rfl le_rfl) (iSup₂_mono' fun t ht => ⟨t, ht.le, le_rfl⟩)
  · refine iSup₂_le fun t ht => ?_
    rcases lt_or_eq_of_le ht with h | rfl
    · exact le_sup_of_le_right (le_iSup₂_of_le t h le_rfl)
    · exact le_sup_left

end Slopes

end

end DiffOp

end GaloisForLFunctions.HTGeometry
