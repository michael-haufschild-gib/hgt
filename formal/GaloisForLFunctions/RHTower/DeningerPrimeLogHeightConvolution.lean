import GaloisForLFunctions.RHTower.DeningerPrimeLogHeightKothe

/-!
# Convolution on the prime-log height source

The exponent lattice is a group, so its Köthe completion carries the convolution
`(a * b)_r = ∑_m a_m b_{r-m}`.  Submultiplicativity of the height turns every weighted `ℓ¹`
seminorm into a submultiplicative one:

`p_k(a * b) ≤ p_k(a) · p_k(b)`.

The shear `(m, n) ↦ (m + n, m)` of the lattice square converts the double series for the
convolution into a product series, which is what makes both the summability and the estimate
work; the same shear gives associativity.

* `deningerHeightConv` : the convolution on the source.
* `deningerHeightSeminorm_conv_le` : **submultiplicativity of every seminorm.**
* `deningerHeightConv_comm`, `deningerHeightConv_assoc`, `deningerHeightConv_delta_zero_left` :
  the algebra laws.
-/

namespace RHTower

open GaloisForLFunctions

noncomputable section

/-- The shear equivalence `(m, n) ↦ (m + n, m)` of the exponent lattice square. -/
def deningerHeightShear : DeningerPrimeLattice × DeningerPrimeLattice ≃ DeningerPrimeLattice × DeningerPrimeLattice where
  toFun q := (q.1 + q.2, q.1)
  invFun q := (q.2, q.1 - q.2)
  left_inv q := by
    refine Prod.ext rfl ?_
    show q.1 + q.2 - q.1 = q.2
    abel
  right_inv q := by
    refine Prod.ext ?_ rfl
    show q.2 + (q.1 - q.2) = q.1
    abel

@[simp]
theorem deningerHeightShear_symm_apply (q : DeningerPrimeLattice × DeningerPrimeLattice) :
    deningerHeightShear.symm q = (q.2, q.1 - q.2) := rfl

/-! ## Summability of the double series -/

private theorem deningerHeightProd_summable (a b : DeningerHeightKothe) (k : ℕ) :
    Summable fun q : DeningerPrimeLattice × DeningerPrimeLattice =>
      (deningerHeight q.1 ^ k * ‖(a : DeningerPrimeLattice → ℂ) q.1‖) *
        (deningerHeight q.2 ^ k * ‖(b : DeningerPrimeLattice → ℂ) q.2‖) := by
  refine Summable.mul_of_nonneg
    (f := fun m : DeningerPrimeLattice => deningerHeight m ^ k * ‖(a : DeningerPrimeLattice → ℂ) m‖)
    (g := fun m : DeningerPrimeLattice => deningerHeight m ^ k * ‖(b : DeningerPrimeLattice → ℂ) m‖)
    (a.2 k) (b.2 k) ?_ ?_
  · intro m
    exact mul_nonneg (pow_nonneg (deningerHeight_pos m).le _) (norm_nonneg _)
  · intro m
    exact mul_nonneg (pow_nonneg (deningerHeight_pos m).le _) (norm_nonneg _)

private theorem deningerHeightShear_summable (a b : DeningerHeightKothe) (k : ℕ) :
    Summable fun q : DeningerPrimeLattice × DeningerPrimeLattice =>
      (deningerHeight q.2 ^ k * ‖(a : DeningerPrimeLattice → ℂ) q.2‖) *
        (deningerHeight (q.1 - q.2) ^ k *
          ‖(b : DeningerPrimeLattice → ℂ) (q.1 - q.2)‖) :=
  (deningerHeightShear.symm.summable_iff
    (f := fun q : DeningerPrimeLattice × DeningerPrimeLattice =>
      (deningerHeight q.1 ^ k * ‖(a : DeningerPrimeLattice → ℂ) q.1‖) *
        (deningerHeight q.2 ^ k * ‖(b : DeningerPrimeLattice → ℂ) q.2‖))).mpr
    (deningerHeightProd_summable a b k)

private theorem deningerHeightConv_norm_summable (a b : DeningerHeightKothe)
    (r : DeningerPrimeLattice) :
    Summable fun m : DeningerPrimeLattice =>
      ‖(a : DeningerPrimeLattice → ℂ) m‖ * ‖(b : DeningerPrimeLattice → ℂ) (r - m)‖ := by
  have h := (deningerHeightShear_summable a b 0).prod_factor r
  refine h.congr fun m => ?_
  simp

private theorem deningerHeightConv_fiber_summable (a b : DeningerHeightKothe)
    (r : DeningerPrimeLattice) :
    Summable fun m : DeningerPrimeLattice =>
      (a : DeningerPrimeLattice → ℂ) m * (b : DeningerPrimeLattice → ℂ) (r - m) := by
  refine Summable.of_norm_bounded (deningerHeightConv_norm_summable a b r) fun m => ?_
  rw [norm_mul]

/-! ## The convolution -/

/-- The coefficient sequence of the convolution `(a * b)_r = ∑_m a_m b_{r-m}`. -/
def deningerHeightConvCoe (a b : DeningerHeightKothe) : DeningerPrimeLattice → ℂ :=
  fun r => ∑' m, (a : DeningerPrimeLattice → ℂ) m * (b : DeningerPrimeLattice → ℂ) (r - m)

private theorem deningerHeightConv_coord_le (a b : DeningerHeightKothe) (k : ℕ)
    (r : DeningerPrimeLattice) :
    deningerHeight r ^ k * ‖deningerHeightConvCoe a b r‖
      ≤ ∑' m : DeningerPrimeLattice,
          (deningerHeight m ^ k * ‖(a : DeningerPrimeLattice → ℂ) m‖) *
            (deningerHeight (r - m) ^ k * ‖(b : DeningerPrimeLattice → ℂ) (r - m)‖) := by
  have hnormSummable : Summable fun m : DeningerPrimeLattice =>
      ‖(a : DeningerPrimeLattice → ℂ) m * (b : DeningerPrimeLattice → ℂ) (r - m)‖ := by
    refine (deningerHeightConv_norm_summable a b r).congr fun m => ?_
    rw [norm_mul]
  have hnorm : ‖deningerHeightConvCoe a b r‖
      ≤ ∑' m : DeningerPrimeLattice,
          ‖(a : DeningerPrimeLattice → ℂ) m‖ * ‖(b : DeningerPrimeLattice → ℂ) (r - m)‖ := by
    refine le_trans (norm_tsum_le_tsum_norm hnormSummable) (le_of_eq (tsum_congr fun m => ?_))
    rw [norm_mul]
  have hheight : (0 : ℝ) ≤ deningerHeight r ^ k := pow_nonneg (deningerHeight_pos r).le _
  calc deningerHeight r ^ k * ‖deningerHeightConvCoe a b r‖
      ≤ deningerHeight r ^ k *
          ∑' m : DeningerPrimeLattice,
            ‖(a : DeningerPrimeLattice → ℂ) m‖ * ‖(b : DeningerPrimeLattice → ℂ) (r - m)‖ :=
        mul_le_mul_of_nonneg_left hnorm hheight
    _ = ∑' m : DeningerPrimeLattice,
          deningerHeight r ^ k *
            (‖(a : DeningerPrimeLattice → ℂ) m‖ * ‖(b : DeningerPrimeLattice → ℂ) (r - m)‖) :=
        (Summable.tsum_mul_left _ (deningerHeightConv_norm_summable a b r)).symm
    _ ≤ ∑' m : DeningerPrimeLattice,
          (deningerHeight m ^ k * ‖(a : DeningerPrimeLattice → ℂ) m‖) *
            (deningerHeight (r - m) ^ k * ‖(b : DeningerPrimeLattice → ℂ) (r - m)‖) := by
        refine Summable.tsum_le_tsum (fun m => ?_)
          ((deningerHeightConv_norm_summable a b r).mul_left _)
          ((deningerHeightShear_summable a b k).prod_factor r)
        have hadd : deningerHeight r ≤ deningerHeight m * deningerHeight (r - m) := by
          have h := deningerHeight_add_le m (r - m)
          rwa [add_sub_cancel] at h
        have hsub : deningerHeight r ^ k
            ≤ deningerHeight m ^ k * deningerHeight (r - m) ^ k := by
          calc deningerHeight r ^ k
              ≤ (deningerHeight m * deningerHeight (r - m)) ^ k :=
                pow_le_pow_left₀ (deningerHeight_pos r).le hadd k
            _ = deningerHeight m ^ k * deningerHeight (r - m) ^ k := mul_pow _ _ _
        have hnn : (0 : ℝ) ≤ ‖(a : DeningerPrimeLattice → ℂ) m‖ *
            ‖(b : DeningerPrimeLattice → ℂ) (r - m)‖ :=
          mul_nonneg (norm_nonneg _) (norm_nonneg _)
        calc deningerHeight r ^ k *
              (‖(a : DeningerPrimeLattice → ℂ) m‖ * ‖(b : DeningerPrimeLattice → ℂ) (r - m)‖)
            ≤ (deningerHeight m ^ k * deningerHeight (r - m) ^ k) *
                (‖(a : DeningerPrimeLattice → ℂ) m‖ * ‖(b : DeningerPrimeLattice → ℂ) (r - m)‖) :=
              mul_le_mul_of_nonneg_right hsub hnn
          _ = (deningerHeight m ^ k * ‖(a : DeningerPrimeLattice → ℂ) m‖) *
                (deningerHeight (r - m) ^ k * ‖(b : DeningerPrimeLattice → ℂ) (r - m)‖) := by
              ring

private theorem deningerHeightConv_mem (a b : DeningerHeightKothe) :
    deningerHeightConvCoe a b ∈ DeningerHeightKothe := by
  intro k
  refine Summable.of_nonneg_of_le
    (fun r => mul_nonneg (pow_nonneg (deningerHeight_pos r).le _) (norm_nonneg _))
    (fun r => deningerHeightConv_coord_le a b k r) ?_
  exact (deningerHeightShear_summable a b k).prod

/-- **The convolution** `(a * b)_r = ∑_m a_m b_{r-m}` on the prime-log height source. -/
def deningerHeightConv (a b : DeningerHeightKothe) : DeningerHeightKothe :=
  ⟨deningerHeightConvCoe a b, deningerHeightConv_mem a b⟩

@[simp]
theorem deningerHeightConv_coe (a b : DeningerHeightKothe) (r : DeningerPrimeLattice) :
    ((deningerHeightConv a b : DeningerHeightKothe) : DeningerPrimeLattice → ℂ) r
      = ∑' m, (a : DeningerPrimeLattice → ℂ) m * (b : DeningerPrimeLattice → ℂ) (r - m) := rfl

/-! ## Submultiplicativity -/

/-- **Every height seminorm is submultiplicative for the convolution.** -/
theorem deningerHeightSeminorm_conv_le (k : ℕ) (a b : DeningerHeightKothe) :
    deningerHeightSeminorm k (deningerHeightConv a b)
      ≤ deningerHeightSeminorm k a * deningerHeightSeminorm k b := by
  have hshear := deningerHeightShear_summable a b k
  have hprodNormA : Summable fun m : DeningerPrimeLattice =>
      ‖deningerHeight m ^ k * ‖(a : DeningerPrimeLattice → ℂ) m‖‖ := by
    refine (a.2 k).congr fun m => ?_
    show deningerHeightKotheData.w k m * ‖(a : DeningerPrimeLattice → ℂ) m‖
        = ‖deningerHeight m ^ k * ‖(a : DeningerPrimeLattice → ℂ) m‖‖
    rw [deningerHeightKotheData_w,
      Real.norm_of_nonneg (mul_nonneg (pow_nonneg (deningerHeight_pos m).le _)
        (norm_nonneg _))]
  have hprodNormB : Summable fun m : DeningerPrimeLattice =>
      ‖deningerHeight m ^ k * ‖(b : DeningerPrimeLattice → ℂ) m‖‖ := by
    refine (b.2 k).congr fun m => ?_
    show deningerHeightKotheData.w k m * ‖(b : DeningerPrimeLattice → ℂ) m‖
        = ‖deningerHeight m ^ k * ‖(b : DeningerPrimeLattice → ℂ) m‖‖
    rw [deningerHeightKotheData_w,
      Real.norm_of_nonneg (mul_nonneg (pow_nonneg (deningerHeight_pos m).le _)
        (norm_nonneg _))]
  have hstep :
      deningerHeightSeminorm k (deningerHeightConv a b)
        ≤ ∑' r : DeningerPrimeLattice, ∑' m : DeningerPrimeLattice,
            (deningerHeight m ^ k * ‖(a : DeningerPrimeLattice → ℂ) m‖) *
              (deningerHeight (r - m) ^ k * ‖(b : DeningerPrimeLattice → ℂ) (r - m)‖) := by
    rw [deningerHeightSeminorm_apply]
    exact Summable.tsum_le_tsum (fun r => deningerHeightConv_coord_le a b k r)
      ((deningerHeightConv a b).2 k) hshear.prod
  have hfubini :
      ∑' r : DeningerPrimeLattice, ∑' m : DeningerPrimeLattice,
          (deningerHeight m ^ k * ‖(a : DeningerPrimeLattice → ℂ) m‖) *
            (deningerHeight (r - m) ^ k * ‖(b : DeningerPrimeLattice → ℂ) (r - m)‖)
        = ∑' q : DeningerPrimeLattice × DeningerPrimeLattice,
            (deningerHeight q.2 ^ k * ‖(a : DeningerPrimeLattice → ℂ) q.2‖) *
              (deningerHeight (q.1 - q.2) ^ k *
                ‖(b : DeningerPrimeLattice → ℂ) (q.1 - q.2)‖) :=
    (hshear.tsum_prod' (fun r => hshear.prod_factor r)).symm
  have hreindex :
      ∑' q : DeningerPrimeLattice × DeningerPrimeLattice,
          (deningerHeight q.2 ^ k * ‖(a : DeningerPrimeLattice → ℂ) q.2‖) *
            (deningerHeight (q.1 - q.2) ^ k *
              ‖(b : DeningerPrimeLattice → ℂ) (q.1 - q.2)‖)
        = ∑' q : DeningerPrimeLattice × DeningerPrimeLattice,
            (deningerHeight q.1 ^ k * ‖(a : DeningerPrimeLattice → ℂ) q.1‖) *
              (deningerHeight q.2 ^ k * ‖(b : DeningerPrimeLattice → ℂ) q.2‖) :=
    deningerHeightShear.symm.tsum_eq
      (fun q : DeningerPrimeLattice × DeningerPrimeLattice =>
        (deningerHeight q.1 ^ k * ‖(a : DeningerPrimeLattice → ℂ) q.1‖) *
          (deningerHeight q.2 ^ k * ‖(b : DeningerPrimeLattice → ℂ) q.2‖))
  have hproduct :
      ∑' q : DeningerPrimeLattice × DeningerPrimeLattice,
          (deningerHeight q.1 ^ k * ‖(a : DeningerPrimeLattice → ℂ) q.1‖) *
            (deningerHeight q.2 ^ k * ‖(b : DeningerPrimeLattice → ℂ) q.2‖)
        = deningerHeightSeminorm k a * deningerHeightSeminorm k b := by
    rw [deningerHeightSeminorm_apply, deningerHeightSeminorm_apply]
    exact (tsum_mul_tsum_of_summable_norm hprodNormA hprodNormB).symm
  rw [hfubini, hreindex, hproduct] at hstep
  exact hstep

/-! ## Bilinearity -/

theorem deningerHeightConv_add_left (a₁ a₂ b : DeningerHeightKothe) :
    deningerHeightConv (a₁ + a₂) b
      = deningerHeightConv a₁ b + deningerHeightConv a₂ b := by
  ext r
  have hL : ((deningerHeightConv (a₁ + a₂) b : DeningerHeightKothe) :
        DeningerPrimeLattice → ℂ) r
      = ∑' m, ((a₁ : DeningerPrimeLattice → ℂ) m * (b : DeningerPrimeLattice → ℂ) (r - m)
          + (a₂ : DeningerPrimeLattice → ℂ) m * (b : DeningerPrimeLattice → ℂ) (r - m)) := by
    rw [deningerHeightConv_coe]
    refine tsum_congr fun m => ?_
    simp only [Submodule.coe_add, Pi.add_apply]
    ring
  rw [hL, Summable.tsum_add (deningerHeightConv_fiber_summable a₁ b r)
    (deningerHeightConv_fiber_summable a₂ b r)]
  simp only [Submodule.coe_add, Pi.add_apply, deningerHeightConv_coe]

theorem deningerHeightConv_add_right (a b₁ b₂ : DeningerHeightKothe) :
    deningerHeightConv a (b₁ + b₂)
      = deningerHeightConv a b₁ + deningerHeightConv a b₂ := by
  ext r
  have hL : ((deningerHeightConv a (b₁ + b₂) : DeningerHeightKothe) :
        DeningerPrimeLattice → ℂ) r
      = ∑' m, ((a : DeningerPrimeLattice → ℂ) m * (b₁ : DeningerPrimeLattice → ℂ) (r - m)
          + (a : DeningerPrimeLattice → ℂ) m * (b₂ : DeningerPrimeLattice → ℂ) (r - m)) := by
    rw [deningerHeightConv_coe]
    refine tsum_congr fun m => ?_
    simp only [Submodule.coe_add, Pi.add_apply]
    ring
  rw [hL, Summable.tsum_add (deningerHeightConv_fiber_summable a b₁ r)
    (deningerHeightConv_fiber_summable a b₂ r)]
  simp only [Submodule.coe_add, Pi.add_apply, deningerHeightConv_coe]

theorem deningerHeightConv_smul_left (c : ℂ) (a b : DeningerHeightKothe) :
    deningerHeightConv (c • a) b = c • deningerHeightConv a b := by
  ext r
  show (∑' m, ((c • a : DeningerHeightKothe) : DeningerPrimeLattice → ℂ) m *
      (b : DeningerPrimeLattice → ℂ) (r - m))
    = ((c • deningerHeightConv a b : DeningerHeightKothe) : DeningerPrimeLattice → ℂ) r
  have hfun : ∀ m : DeningerPrimeLattice,
      ((c • a : DeningerHeightKothe) : DeningerPrimeLattice → ℂ) m *
        (b : DeningerPrimeLattice → ℂ) (r - m)
        = c * ((a : DeningerPrimeLattice → ℂ) m * (b : DeningerPrimeLattice → ℂ) (r - m)) := by
    intro m
    show c * (a : DeningerPrimeLattice → ℂ) m * (b : DeningerPrimeLattice → ℂ) (r - m)
        = c * ((a : DeningerPrimeLattice → ℂ) m * (b : DeningerPrimeLattice → ℂ) (r - m))
    ring
  rw [tsum_congr hfun,
    Summable.tsum_mul_left c (deningerHeightConv_fiber_summable a b r)]
  rfl

theorem deningerHeightConv_smul_right (c : ℂ) (a b : DeningerHeightKothe) :
    deningerHeightConv a (c • b) = c • deningerHeightConv a b := by
  ext r
  show (∑' m, (a : DeningerPrimeLattice → ℂ) m *
      ((c • b : DeningerHeightKothe) : DeningerPrimeLattice → ℂ) (r - m))
    = ((c • deningerHeightConv a b : DeningerHeightKothe) : DeningerPrimeLattice → ℂ) r
  have hfun : ∀ m : DeningerPrimeLattice,
      (a : DeningerPrimeLattice → ℂ) m *
        ((c • b : DeningerHeightKothe) : DeningerPrimeLattice → ℂ) (r - m)
        = c * ((a : DeningerPrimeLattice → ℂ) m * (b : DeningerPrimeLattice → ℂ) (r - m)) := by
    intro m
    show (a : DeningerPrimeLattice → ℂ) m * (c * (b : DeningerPrimeLattice → ℂ) (r - m))
        = c * ((a : DeningerPrimeLattice → ℂ) m * (b : DeningerPrimeLattice → ℂ) (r - m))
    ring
  rw [tsum_congr hfun,
    Summable.tsum_mul_left c (deningerHeightConv_fiber_summable a b r)]
  rfl

/-! ## Commutativity and unit -/

theorem deningerHeightConv_comm (a b : DeningerHeightKothe) :
    deningerHeightConv a b = deningerHeightConv b a := by
  ext r
  show (∑' m, (a : DeningerPrimeLattice → ℂ) m * (b : DeningerPrimeLattice → ℂ) (r - m))
      = ∑' m, (b : DeningerPrimeLattice → ℂ) m * (a : DeningerPrimeLattice → ℂ) (r - m)
  rw [← (Equiv.subLeft r).tsum_eq
    (fun m : DeningerPrimeLattice =>
      (b : DeningerPrimeLattice → ℂ) m * (a : DeningerPrimeLattice → ℂ) (r - m))]
  refine tsum_congr fun m => ?_
  show (a : DeningerPrimeLattice → ℂ) m * (b : DeningerPrimeLattice → ℂ) (r - m)
      = (b : DeningerPrimeLattice → ℂ) (r - m) * (a : DeningerPrimeLattice → ℂ) (r - (r - m))
  rw [sub_sub_cancel, mul_comm]

/-- The unit of the convolution is the basis vector at the zero character. -/
theorem deningerHeightConv_delta_zero_left (b : DeningerHeightKothe) :
    deningerHeightConv (deningerKotheDelta deningerHeightKotheData 0) b = b := by
  classical
  ext r
  show (∑' m, ((deningerKotheDelta deningerHeightKotheData 0 : DeningerHeightKothe) :
      DeningerPrimeLattice → ℂ) m * (b : DeningerPrimeLattice → ℂ) (r - m))
      = (b : DeningerPrimeLattice → ℂ) r
  rw [tsum_eq_single 0]
  · rw [deningerKotheDelta_coe]
    simp
  · intro m hm
    have hzero : ((deningerKotheDelta deningerHeightKotheData 0 : DeningerHeightKothe) :
        DeningerPrimeLattice → ℂ) m = 0 := by
      rw [deningerKotheDelta_coe]
      exact Pi.single_eq_of_ne hm 1
    rw [hzero, zero_mul]

/-! ## Associativity -/

private theorem deningerHeightTriple_summable (a b c : DeningerHeightKothe)
    (s : DeningerPrimeLattice) :
    Summable fun q : DeningerPrimeLattice × DeningerPrimeLattice =>
      (a : DeningerPrimeLattice → ℂ) q.1 * (b : DeningerPrimeLattice → ℂ) q.2 *
        (c : DeningerPrimeLattice → ℂ) (s - q.1 - q.2) := by
  have hbound : ∀ x : DeningerPrimeLattice,
      ‖(c : DeningerPrimeLattice → ℂ) x‖ ≤ deningerHeightSeminorm 0 c := by
    intro x
    have h := deningerHeightSeminorm_coord_le 0 c x
    rwa [pow_zero, one_mul] at h
  have ha0 : Summable fun m : DeningerPrimeLattice => ‖(a : DeningerPrimeLattice → ℂ) m‖ := by
    refine (a.2 0).congr fun m => ?_
    show deningerHeightKotheData.w 0 m * ‖(a : DeningerPrimeLattice → ℂ) m‖
        = ‖(a : DeningerPrimeLattice → ℂ) m‖
    rw [deningerHeightKotheData_w, pow_zero, one_mul]
  have hb0 : Summable fun m : DeningerPrimeLattice => ‖(b : DeningerPrimeLattice → ℂ) m‖ := by
    refine (b.2 0).congr fun m => ?_
    show deningerHeightKotheData.w 0 m * ‖(b : DeningerPrimeLattice → ℂ) m‖
        = ‖(b : DeningerPrimeLattice → ℂ) m‖
    rw [deningerHeightKotheData_w, pow_zero, one_mul]
  have hprod : Summable fun q : DeningerPrimeLattice × DeningerPrimeLattice =>
      ‖(a : DeningerPrimeLattice → ℂ) q.1‖ * ‖(b : DeningerPrimeLattice → ℂ) q.2‖ :=
    Summable.mul_of_nonneg
      (f := fun m : DeningerPrimeLattice => ‖(a : DeningerPrimeLattice → ℂ) m‖)
      (g := fun m : DeningerPrimeLattice => ‖(b : DeningerPrimeLattice → ℂ) m‖)
      ha0 hb0 (fun m => norm_nonneg _) (fun m => norm_nonneg _)
  refine Summable.of_norm_bounded (hprod.mul_right (deningerHeightSeminorm 0 c)) fun q => ?_
  rw [norm_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (hbound _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))

private theorem deningerHeightTripleShear_summable (a b c : DeningerHeightKothe)
    (s : DeningerPrimeLattice) :
    Summable fun q : DeningerPrimeLattice × DeningerPrimeLattice =>
      (a : DeningerPrimeLattice → ℂ) q.2 * (b : DeningerPrimeLattice → ℂ) (q.1 - q.2) *
        (c : DeningerPrimeLattice → ℂ) (s - q.1) := by
  have h := (deningerHeightShear.symm.summable_iff
    (f := fun q : DeningerPrimeLattice × DeningerPrimeLattice =>
      (a : DeningerPrimeLattice → ℂ) q.1 * (b : DeningerPrimeLattice → ℂ) q.2 *
        (c : DeningerPrimeLattice → ℂ) (s - q.1 - q.2))).mpr
    (deningerHeightTriple_summable a b c s)
  refine h.congr fun q => ?_
  have hindex : s - q.2 - (q.1 - q.2) = s - q.1 := by abel
  show (a : DeningerPrimeLattice → ℂ) q.2 * (b : DeningerPrimeLattice → ℂ) (q.1 - q.2) *
      (c : DeningerPrimeLattice → ℂ) (s - q.2 - (q.1 - q.2))
      = (a : DeningerPrimeLattice → ℂ) q.2 * (b : DeningerPrimeLattice → ℂ) (q.1 - q.2) *
        (c : DeningerPrimeLattice → ℂ) (s - q.1)
  rw [hindex]

theorem deningerHeightConv_assoc (a b c : DeningerHeightKothe) :
    deningerHeightConv (deningerHeightConv a b) c
      = deningerHeightConv a (deningerHeightConv b c) := by
  ext s
  have hT := deningerHeightTriple_summable a b c s
  have hU := deningerHeightTripleShear_summable a b c s
  have hleft :
      ((deningerHeightConv (deningerHeightConv a b) c : DeningerHeightKothe) :
          DeningerPrimeLattice → ℂ) s
        = ∑' q : DeningerPrimeLattice × DeningerPrimeLattice,
            (a : DeningerPrimeLattice → ℂ) q.2 * (b : DeningerPrimeLattice → ℂ) (q.1 - q.2) *
              (c : DeningerPrimeLattice → ℂ) (s - q.1) := by
    rw [deningerHeightConv_coe]
    rw [hU.tsum_prod' (fun r => hU.prod_factor r)]
    refine tsum_congr fun r => ?_
    show (∑' m, (a : DeningerPrimeLattice → ℂ) m * (b : DeningerPrimeLattice → ℂ) (r - m)) *
        (c : DeningerPrimeLattice → ℂ) (s - r)
      = ∑' m, (a : DeningerPrimeLattice → ℂ) m * (b : DeningerPrimeLattice → ℂ) (r - m) *
          (c : DeningerPrimeLattice → ℂ) (s - r)
    exact (Summable.tsum_mul_right _ (deningerHeightConv_fiber_summable a b r)).symm
  have hright :
      ((deningerHeightConv a (deningerHeightConv b c) : DeningerHeightKothe) :
          DeningerPrimeLattice → ℂ) s
        = ∑' q : DeningerPrimeLattice × DeningerPrimeLattice,
            (a : DeningerPrimeLattice → ℂ) q.1 * (b : DeningerPrimeLattice → ℂ) q.2 *
              (c : DeningerPrimeLattice → ℂ) (s - q.1 - q.2) := by
    rw [deningerHeightConv_coe]
    rw [hT.tsum_prod' (fun m => hT.prod_factor m)]
    refine tsum_congr fun m => ?_
    show (a : DeningerPrimeLattice → ℂ) m *
        (∑' n, (b : DeningerPrimeLattice → ℂ) n * (c : DeningerPrimeLattice → ℂ) (s - m - n))
      = ∑' n, (a : DeningerPrimeLattice → ℂ) m * (b : DeningerPrimeLattice → ℂ) n *
          (c : DeningerPrimeLattice → ℂ) (s - m - n)
    rw [← Summable.tsum_mul_left _ (deningerHeightConv_fiber_summable b c (s - m))]
    refine tsum_congr fun n => ?_
    ring
  have hcong :
      ∑' q : DeningerPrimeLattice × DeningerPrimeLattice,
          (a : DeningerPrimeLattice → ℂ) q.2 * (b : DeningerPrimeLattice → ℂ) (q.1 - q.2) *
            (c : DeningerPrimeLattice → ℂ) (s - q.1)
        = ∑' q : DeningerPrimeLattice × DeningerPrimeLattice,
            (a : DeningerPrimeLattice → ℂ) (deningerHeightShear.symm q).1 *
              (b : DeningerPrimeLattice → ℂ) (deningerHeightShear.symm q).2 *
              (c : DeningerPrimeLattice → ℂ)
                (s - (deningerHeightShear.symm q).1 - (deningerHeightShear.symm q).2) := by
    refine tsum_congr fun q => ?_
    have hindex : s - q.1 = s - q.2 - (q.1 - q.2) := by abel
    simp only [deningerHeightShear_symm_apply, hindex]
  rw [hleft, hright, hcong]
  exact deningerHeightShear.symm.tsum_eq
    (fun q : DeningerPrimeLattice × DeningerPrimeLattice =>
      (a : DeningerPrimeLattice → ℂ) q.1 * (b : DeningerPrimeLattice → ℂ) q.2 *
        (c : DeningerPrimeLattice → ℂ) (s - q.1 - q.2))

end

end RHTower
