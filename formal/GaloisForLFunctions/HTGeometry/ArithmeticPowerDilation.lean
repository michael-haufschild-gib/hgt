import GaloisForLFunctions.RHTower.MFreeTower

/-!
# Power dilation preserves Dirichlet convolution

The cube-completion inversion in Lemma 5.3 of *The Quasi-Riemann Hypothesis*
uses multiplicative reindexing before Möbius cancellation.  The existing `mPart`
operation has this stronger algebraic property for every positive exponent:
it is an injective ring homomorphism for Dirichlet convolution.  Thus arbitrary
convolution identities, not only identities of multiplicative functions, lift
to the power-supported subalgebra.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction
open scoped BigOperators ArithmeticFunction.zeta Moebius

/-- Power dilation preserves convolution, including nonmultiplicative coefficients. -/
theorem mPart_mul_succ {R : Type*} [Semiring R] (m : ℕ)
    (f g : ArithmeticFunction R) :
    mPart (m + 1) (f * g) = mPart (m + 1) f * mPart (m + 1) g := by
  classical
  have hinj := Nat.pow_left_injective (Nat.succ_ne_zero m)
  ext n
  by_cases hn : ∃ k, k ^ (m + 1) = n
  · obtain ⟨k, rfl⟩ := hn
    rw [mPart_apply_pow (Nat.succ_ne_zero m), ArithmeticFunction.mul_apply,
      ArithmeticFunction.mul_apply]
    let lift : ℕ × ℕ → ℕ × ℕ := fun ab => (ab.1 ^ (m + 1), ab.2 ^ (m + 1))
    have hsub : k.divisorsAntidiagonal.image lift ⊆
        (k ^ (m + 1)).divisorsAntidiagonal := by
      intro ab hab
      obtain ⟨cd, hcd, rfl⟩ := Finset.mem_image.mp hab
      obtain ⟨hprod, hk⟩ := Nat.mem_divisorsAntidiagonal.mp hcd
      exact Nat.mem_divisorsAntidiagonal.mpr
        ⟨by simp only [lift, ← mul_pow, hprod], pow_ne_zero _ hk⟩
    have hzero : ∀ ab ∈ (k ^ (m + 1)).divisorsAntidiagonal,
        ab ∉ k.divisorsAntidiagonal.image lift →
        mPart (m + 1) f ab.1 * mPart (m + 1) g ab.2 = 0 := by
      intro ab hab hnot
      by_cases ha : ∃ a, a ^ (m + 1) = ab.1
      · obtain ⟨a, ha⟩ := ha
        have hb : ∀ b, b ^ (m + 1) ≠ ab.2 := by
          intro b hb
          apply hnot
          apply Finset.mem_image.mpr
          refine ⟨(a, b), Nat.mem_divisorsAntidiagonal.mpr ⟨?_, ?_⟩, ?_⟩
          · apply hinj
            simpa only [mul_pow, ha, hb] using
              (Nat.mem_divisorsAntidiagonal.mp hab).1
          · intro hk
            exact (Nat.mem_divisorsAntidiagonal.mp hab).2 (by simp [hk])
          · exact Prod.ext ha hb
        rw [mPart_apply_of_forall_pow_ne _ g hb, mul_zero]
      · rw [mPart_apply_of_forall_pow_ne _ f (fun a ha' => ha ⟨a, ha'⟩), zero_mul]
    rw [← Finset.sum_subset hsub hzero, Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro ab _
      simp only [lift, mPart_apply_pow (Nat.succ_ne_zero m)]
    · intro ab _ cd _ h
      exact Prod.ext (hinj (congrArg Prod.fst h)) (hinj (congrArg Prod.snd h))
  · rw [mPart_apply_of_forall_pow_ne _ (f * g) (fun k hk => hn ⟨k, hk⟩),
      ArithmeticFunction.mul_apply]
    symm
    apply Finset.sum_eq_zero
    intro ab hab
    by_cases ha : ∃ a, a ^ (m + 1) = ab.1
    · obtain ⟨a, ha⟩ := ha
      have hb : ∀ b, b ^ (m + 1) ≠ ab.2 := by
        intro b hb
        apply hn
        exact ⟨a * b, by simpa only [mul_pow, ha, hb] using
          (Nat.mem_divisorsAntidiagonal.mp hab).1⟩
      rw [mPart_apply_of_forall_pow_ne _ g hb, mul_zero]
    · rw [mPart_apply_of_forall_pow_ne _ f (fun a ha' => ha ⟨a, ha'⟩), zero_mul]

/-- Positive power dilation as a homomorphism of convolution semirings. -/
def powerDilationRingHom {R : Type*} [Semiring R] (m : ℕ) :
    ArithmeticFunction R →+* ArithmeticFunction R where
  toFun := mPart (m + 1)
  map_zero' := by ext n; simp [mPart_apply]
  map_add' f g := by
    ext n
    simp only [mPart_apply, ArithmeticFunction.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> simp
  map_one' := by
    ext n
    by_cases hn : ∃ k, k ^ (m + 1) = n
    · obtain ⟨k, rfl⟩ := hn
      rw [mPart_apply_pow (Nat.succ_ne_zero m)]
      by_cases hk : k = 1
      · simp [hk]
      · simp [hk]
    · have hn1 : n ≠ 1 := by intro h; exact hn ⟨1, by simp [h]⟩
      rw [mPart_apply_of_forall_pow_ne _ _ (fun k hk => hn ⟨k, hk⟩)]
      simp [hn1]
  map_mul' := mPart_mul_succ m

/-- Dilation loses no coefficient information. -/
theorem powerDilationRingHom_injective {R : Type*} [Semiring R] (m : ℕ) :
    Function.Injective (powerDilationRingHom (R := R) m) := by
  intro f g h
  ext n
  have hn := congrArg (fun a : ArithmeticFunction R => a (n ^ (m + 1))) h
  simpa [powerDilationRingHom, mPart_apply_pow (Nat.succ_ne_zero m)] using hn

/-- Power-supported Möbius inversion, including cube completion at `m = 2`. -/
theorem powerDilation_moebius_zeta_cancel {R : Type*} [Ring R] (m : ℕ)
    (f : ArithmeticFunction R) :
    mPart (m + 1) (μ : ArithmeticFunction R) *
        (mPart (m + 1) (ζ : ArithmeticFunction R) * f) = f := by
  rw [← mul_assoc, ← mPart_mul_succ,
    ArithmeticFunction.coe_moebius_mul_coe_zeta]
  change powerDilationRingHom m 1 * f = f
  rw [map_one, one_mul]

/-- Completely multiplicative coefficient weights act on the convolution algebra.
The weight need not vanish at zero, since arithmetic functions already do. -/
def arithmeticTwistRingHom {R : Type*} [CommSemiring R] (w : ℕ →* R) :
    ArithmeticFunction R →+* ArithmeticFunction R where
  toFun f := ⟨fun n => w n * f n, by simp⟩
  map_zero' := by ext n; simp
  map_one' := by
    ext n
    change w n * (1 : ArithmeticFunction R) n = (1 : ArithmeticFunction R) n
    by_cases hn : n = 1 <;> simp [hn]
  map_add' f g := by
    ext n
    exact mul_add (w n) (f n) (g n)
  map_mul' f g := by
    ext n
    change w n * (f * g) n = _
    rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ab hab
    change w n * (f ab.1 * g ab.2) = (w ab.1 * f ab.1) * (w ab.2 * g ab.2)
    rw [← (Nat.mem_divisorsAntidiagonal.mp hab).1, map_mul]
    ring

/-- Weight a coefficient at its original index, then move it to a positive power. -/
def powerTwistedDilation {R : Type*} [CommSemiring R] (m : ℕ) (w : ℕ →* R) :
    ArithmeticFunction R →+* ArithmeticFunction R :=
  (powerDilationRingHom m).comp (arithmeticTwistRingHom w)

@[simp]
theorem powerTwistedDilation_apply_pow {R : Type*} [CommSemiring R]
    (m : ℕ) (w : ℕ →* R) (f : ArithmeticFunction R) (n : ℕ) :
    powerTwistedDilation m w f (n ^ (m + 1)) = w n * f n := by
  exact mPart_apply_pow (Nat.succ_ne_zero m) _ n

/-- Weighted power completion has an exact Möbius inverse, even when weights vanish. -/
theorem powerTwistedDilation_moebius_zeta_cancel {R : Type*} [CommRing R]
    (m : ℕ) (w : ℕ →* R) (f : ArithmeticFunction R) :
    powerTwistedDilation m w (μ : ArithmeticFunction R) *
        (powerTwistedDilation m w (ζ : ArithmeticFunction R) * f) = f := by
  rw [← mul_assoc, ← map_mul, ArithmeticFunction.coe_moebius_mul_coe_zeta,
    map_one, one_mul]

end RHTower
