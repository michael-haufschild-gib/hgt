import GaloisForLFunctions.RHTower.DeningerPrimeLogHeight
import GaloisForLFunctions.RHTower.DeningerKotheComplete

/-!
# The prime-log height Köthe source

The rational Kummer character lattice `Γ = ℤ^(ℙ)` is completed with the weights `H(m)^k` of its
own multiplicative height.  Because the inverse height is square summable over `Γ`, the resulting
Köthe space is nuclear; it is complete, the finitely supported group algebra is dense, and
reflection and the star operation are seminorm isometries.

* `deningerHeightKotheData`, `deningerHeightSeminorm` : the source and its seminorms.
* `deningerHeightKothe_isNuclearSpace`, `deningerHeightKothe_exists_limit`,
  `deningerHeightKothe_exists_finite_approx` : nuclear, complete, and with dense group algebra.
* `deningerHeightReflect`, `deningerHeightStar` : reflection and star, with their isometries.
* `deningerHeightKotheZero` : the sector of vanishing total character.
-/

namespace RHTower

open GaloisForLFunctions

noncomputable section

/-! ## The source -/

/-- **The prime-log height Köthe datum**: the weights are the powers of the height. -/
def deningerHeightKotheData : DeningerKotheData (Nat.Primes →₀ ℤ) where
  w k m := deningerHeight m ^ k
  pos k m := pow_pos (deningerHeight_pos m) k
  mono k m := pow_le_pow_right₀ (one_le_deningerHeight m) (Nat.le_succ k)

@[simp]
theorem deningerHeightKotheData_w (k : ℕ) (m : Nat.Primes →₀ ℤ) :
    deningerHeightKotheData.w k m = deningerHeight m ^ k := rfl

/-- **The prime-log height source** `𝒦_H`. -/
abbrev DeningerHeightKothe : Submodule ℂ ((Nat.Primes →₀ ℤ) → ℂ) :=
  DeningerKotheCarrier ℂ deningerHeightKotheData

/-- The `k`-th seminorm `p_k(a) = ∑_m H(m)^k |a_m|` of the source. -/
def deningerHeightSeminorm (k : ℕ) : Seminorm ℂ DeningerHeightKothe :=
  deningerKotheSeminorm deningerHeightKotheData k

theorem deningerHeightSeminorm_apply (k : ℕ) (a : DeningerHeightKothe) :
    deningerHeightSeminorm k a
      = ∑' m, deningerHeight m ^ k * ‖(a : (Nat.Primes →₀ ℤ) → ℂ) m‖ := rfl

theorem deningerHeightSeminorm_summable (a : DeningerHeightKothe) (k : ℕ) :
    Summable fun m => deningerHeight m ^ k * ‖(a : (Nat.Primes →₀ ℤ) → ℂ) m‖ :=
  a.2 k

theorem deningerHeightSeminorm_coord_le (k : ℕ) (a : DeningerHeightKothe)
    (m : Nat.Primes →₀ ℤ) :
    deningerHeight m ^ k * ‖(a : (Nat.Primes →₀ ℤ) → ℂ) m‖ ≤ deningerHeightSeminorm k a :=
  deningerKotheSeminorm_coord_le deningerHeightKotheData k a m

theorem deningerHeightSeminorm_mono {k l : ℕ} (h : k ≤ l) (a : DeningerHeightKothe) :
    deningerHeightSeminorm k a ≤ deningerHeightSeminorm l a :=
  deningerKotheSeminorm_le deningerHeightKotheData h a

theorem deningerHeightKothe_summable_norm (a : DeningerHeightKothe) :
    Summable fun m => ‖(a : DeningerLattice → ℂ) m‖ := by
  refine (a.2 0).congr fun m => ?_
  show deningerHeightKotheData.w 0 m * ‖(a : DeningerLattice → ℂ) m‖
      = ‖(a : DeningerLattice → ℂ) m‖
  rw [deningerHeightKotheData_w, pow_zero, one_mul]

theorem deningerHeightKothe_norm_le (a : DeningerHeightKothe) (m : DeningerLattice) :
    ‖(a : DeningerLattice → ℂ) m‖ ≤ deningerHeightSeminorm 0 a := by
  have h := deningerHeightSeminorm_coord_le 0 a m
  rwa [pow_zero, one_mul] at h

theorem deningerHeightSeminorm_zero_eq (a : DeningerHeightKothe) :
    deningerHeightSeminorm 0 a = ∑' m, ‖(a : DeningerLattice → ℂ) m‖ := by
  rw [deningerHeightSeminorm_apply]
  exact tsum_congr fun m => by rw [pow_zero, one_mul]

/-! ## Nuclearity -/

/-- The height weights are summable against two steps later, because the inverse height is square
summable over the exponent lattice. -/
theorem deningerHeightKotheData_isNuclear : deningerHeightKotheData.IsNuclear := by
  intro k
  refine ⟨k + 2, by omega, ?_⟩
  refine deningerHeight_summable_inv_sq.congr fun m => ?_
  have hpos : (0 : ℝ) < deningerHeight m := deningerHeight_pos m
  show (deningerHeight m)⁻¹ ^ 2
      = deningerHeight m ^ k / deningerHeight m ^ (k + 2)
  rw [pow_add, inv_pow]
  rw [eq_div_iff (by positivity)]
  field_simp

/-- **The prime-log height source is nuclear.** -/
theorem deningerHeightKothe_isNuclearSpace :
    DeningerIsNuclearSpace (deningerKotheSeminorm (𝕜 := ℂ) deningerHeightKotheData) := by
  classical
  exact deningerKothe_isNuclearSpace _ deningerHeightKotheData_isNuclear

/-! ## Completeness and density -/

/-- **The prime-log height source is sequentially complete.** -/
theorem deningerHeightKothe_exists_limit (a : ℕ → DeningerHeightKothe)
    (h : DeningerKotheCauchy deningerHeightKotheData a) :
    ∃ L : DeningerHeightKothe, DeningerKotheTendsto deningerHeightKotheData a L :=
  deningerKothe_exists_limit a h

/-- **The finitely supported group algebra is dense in the source.** -/
theorem deningerHeightKothe_exists_finite_approx (a : DeningerHeightKothe) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset (Nat.Primes →₀ ℤ),
      deningerHeightSeminorm k
        (a - ∑ m ∈ S, (a : (Nat.Primes →₀ ℤ) → ℂ) m •
          deningerKotheDelta deningerHeightKotheData m) < ε := by
  classical
  exact deningerKothe_exists_finite_approx a k hε

/-! ## Reflection -/

private theorem deningerHeightReflect_mem (a : DeningerHeightKothe) :
    (fun m => (a : (Nat.Primes →₀ ℤ) → ℂ) (-m)) ∈ DeningerHeightKothe := by
  intro k
  have hcomp := (a.2 k).comp_injective (i := fun m : Nat.Primes →₀ ℤ => -m) neg_injective
  refine hcomp.congr fun m => ?_
  show deningerHeightKotheData.w k (-m) * ‖(a : (Nat.Primes →₀ ℤ) → ℂ) (-m)‖
      = deningerHeightKotheData.w k m * ‖(a : (Nat.Primes →₀ ℤ) → ℂ) (-m)‖
  rw [deningerHeightKotheData_w, deningerHeightKotheData_w, deningerHeight_neg]

/-- **Reflection** `(Ra)_m = a_{-m}` on the source. -/
def deningerHeightReflect : DeningerHeightKothe →ₗ[ℂ] DeningerHeightKothe where
  toFun a := ⟨fun m => (a : (Nat.Primes →₀ ℤ) → ℂ) (-m), deningerHeightReflect_mem a⟩
  map_add' a b := by
    ext m
    show (a : (Nat.Primes →₀ ℤ) → ℂ) (-m) + (b : (Nat.Primes →₀ ℤ) → ℂ) (-m)
        = ((a + b : DeningerHeightKothe) : (Nat.Primes →₀ ℤ) → ℂ) (-m)
    rw [Submodule.coe_add, Pi.add_apply]
  map_smul' c a := by
    ext m
    show c * (a : (Nat.Primes →₀ ℤ) → ℂ) (-m)
        = ((c • a : DeningerHeightKothe) : (Nat.Primes →₀ ℤ) → ℂ) (-m)
    rfl

@[simp]
theorem deningerHeightReflect_coe (a : DeningerHeightKothe) (m : Nat.Primes →₀ ℤ) :
    ((deningerHeightReflect a : DeningerHeightKothe) : (Nat.Primes →₀ ℤ) → ℂ) m
      = (a : (Nat.Primes →₀ ℤ) → ℂ) (-m) := rfl

/-- Reflection is an involution. -/
theorem deningerHeightReflect_involutive (a : DeningerHeightKothe) :
    deningerHeightReflect (deningerHeightReflect a) = a := by
  ext m
  show (a : (Nat.Primes →₀ ℤ) → ℂ) (- -m) = (a : (Nat.Primes →₀ ℤ) → ℂ) m
  rw [neg_neg]

/-- **Reflection is a seminorm isometry.** -/
theorem deningerHeightSeminorm_reflect (k : ℕ) (a : DeningerHeightKothe) :
    deningerHeightSeminorm k (deningerHeightReflect a) = deningerHeightSeminorm k a := by
  rw [deningerHeightSeminorm_apply, deningerHeightSeminorm_apply]
  rw [← (Equiv.neg (Nat.Primes →₀ ℤ)).tsum_eq
    (fun m => deningerHeight m ^ k * ‖(a : (Nat.Primes →₀ ℤ) → ℂ) m‖)]
  refine tsum_congr fun m => ?_
  show deningerHeight m ^ k * ‖(a : (Nat.Primes →₀ ℤ) → ℂ) (-m)‖
      = deningerHeight (-m) ^ k * ‖(a : (Nat.Primes →₀ ℤ) → ℂ) (-m)‖
  rw [deningerHeight_neg]

/-! ## Star -/

private theorem deningerHeightStar_mem (a : DeningerHeightKothe) :
    (fun m => (starRingEnd ℂ) ((a : (Nat.Primes →₀ ℤ) → ℂ) (-m))) ∈ DeningerHeightKothe := by
  intro k
  have hmem := deningerHeightReflect_mem a k
  refine hmem.congr fun m => ?_
  show deningerHeightKotheData.w k m * ‖(a : (Nat.Primes →₀ ℤ) → ℂ) (-m)‖
      = deningerHeightKotheData.w k m *
        ‖(starRingEnd ℂ) ((a : (Nat.Primes →₀ ℤ) → ℂ) (-m))‖
  rw [RCLike.norm_conj]

/-- **The star operation** `(a*)_m = conj(a_{-m})` on the source. -/
def deningerHeightStar (a : DeningerHeightKothe) : DeningerHeightKothe :=
  ⟨fun m => (starRingEnd ℂ) ((a : (Nat.Primes →₀ ℤ) → ℂ) (-m)), deningerHeightStar_mem a⟩

@[simp]
theorem deningerHeightStar_coe (a : DeningerHeightKothe) (m : Nat.Primes →₀ ℤ) :
    ((deningerHeightStar a : DeningerHeightKothe) : (Nat.Primes →₀ ℤ) → ℂ) m
      = (starRingEnd ℂ) ((a : (Nat.Primes →₀ ℤ) → ℂ) (-m)) := rfl

theorem deningerHeightStar_add (a b : DeningerHeightKothe) :
    deningerHeightStar (a + b) = deningerHeightStar a + deningerHeightStar b := by
  ext m
  show (starRingEnd ℂ) (((a + b : DeningerHeightKothe) : (Nat.Primes →₀ ℤ) → ℂ) (-m))
      = ((deningerHeightStar a + deningerHeightStar b : DeningerHeightKothe) :
          (Nat.Primes →₀ ℤ) → ℂ) m
  rw [Submodule.coe_add, Pi.add_apply, map_add, Submodule.coe_add, Pi.add_apply]
  rfl

theorem deningerHeightStar_smul (c : ℂ) (a : DeningerHeightKothe) :
    deningerHeightStar (c • a) = (starRingEnd ℂ) c • deningerHeightStar a := by
  ext m
  show (starRingEnd ℂ) (((c • a : DeningerHeightKothe) : (Nat.Primes →₀ ℤ) → ℂ) (-m))
      = (((starRingEnd ℂ) c • deningerHeightStar a : DeningerHeightKothe) :
          (Nat.Primes →₀ ℤ) → ℂ) m
  show (starRingEnd ℂ) (c * (a : (Nat.Primes →₀ ℤ) → ℂ) (-m))
      = (starRingEnd ℂ) c * (starRingEnd ℂ) ((a : (Nat.Primes →₀ ℤ) → ℂ) (-m))
  rw [map_mul]

theorem deningerHeightStar_involutive (a : DeningerHeightKothe) :
    deningerHeightStar (deningerHeightStar a) = a := by
  ext m
  show (starRingEnd ℂ) ((starRingEnd ℂ) ((a : (Nat.Primes →₀ ℤ) → ℂ) (- -m)))
      = (a : (Nat.Primes →₀ ℤ) → ℂ) m
  rw [neg_neg, Complex.conj_conj]

/-- **Star is a seminorm isometry.** -/
theorem deningerHeightSeminorm_star (k : ℕ) (a : DeningerHeightKothe) :
    deningerHeightSeminorm k (deningerHeightStar a) = deningerHeightSeminorm k a := by
  rw [← deningerHeightSeminorm_reflect k a, deningerHeightSeminorm_apply,
    deningerHeightSeminorm_apply]
  refine tsum_congr fun m => ?_
  show deningerHeight m ^ k * ‖(starRingEnd ℂ) ((a : (Nat.Primes →₀ ℤ) → ℂ) (-m))‖
      = deningerHeight m ^ k * ‖(a : (Nat.Primes →₀ ℤ) → ℂ) (-m)‖
  rw [RCLike.norm_conj]

/-! ## The zero-character sector -/

/-- **The sector of vanishing total character** `𝒦_H^0 = {a : a_0 = 0}`. -/
def deningerHeightKotheZero : Submodule ℂ DeningerHeightKothe :=
  LinearMap.ker (deningerKotheCoeffLinear (𝕜 := ℂ) deningerHeightKotheData 0)

theorem deningerHeightKotheZero_mem_iff (a : DeningerHeightKothe) :
    a ∈ deningerHeightKotheZero ↔ (a : (Nat.Primes →₀ ℤ) → ℂ) 0 = 0 := Iff.rfl

end

end RHTower
