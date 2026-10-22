import GaloisForLFunctions.RHTower.Deninger.DeningerNuclearCompletedInvariance

/-!
# The space of rapidly decreasing sequences

A sequence is rapidly decreasing when every polynomial multiple of it is square-summable.  Those
sequences form a subspace of all sequences, graded by the family of weighted `ℓ²` seminorms
`‖(n+1)^k a n‖`, each of which is Hilbertian by construction.  The seminorms increase with the
weight, the coordinate of a sequence is controlled by every one of them, and the standard basis
vectors have weighted norm exactly `(n+1)^k`.

This is the model of a nuclear space that is not finite dimensional, and the concrete carrier of
a graded test scale.

* `DeningerRapidCarrier` : the space of rapidly decreasing sequences.
* `deningerRapidSeminorm`, `_hilbertian`, `_le` : the weighted `ℓ²` seminorms.
* `deningerRapidWeight_norm_mul_le` : the coordinate bound.
* `deningerRapidBasis`, `deningerRapidSeminorm_basis` : the standard basis vectors.
-/

namespace RHTower

open scoped ENNReal

section RapidSequences

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The polynomial weight `(n+1)^k`, as a scalar. -/
def deningerRapidWeight (𝕜 : Type*) [RCLike 𝕜] (k n : ℕ) : 𝕜 := ((n + 1 : ℕ) : 𝕜) ^ k

theorem deningerRapidWeight_norm (k n : ℕ) :
    ‖deningerRapidWeight 𝕜 k n‖ = ((n : ℝ) + 1) ^ k := by
  rw [deningerRapidWeight, norm_pow, RCLike.norm_natCast]
  push_cast
  ring

theorem deningerRapidWeight_norm_pos (k n : ℕ) : 0 < ‖deningerRapidWeight 𝕜 k n‖ := by
  rw [deningerRapidWeight_norm]
  positivity

/-- **The space of rapidly decreasing sequences**: those all of whose polynomial multiples are
square-summable. -/
def DeningerRapidCarrier (𝕜 : Type*) [RCLike 𝕜] : Submodule 𝕜 (ℕ → 𝕜) where
  carrier := {a | ∀ k : ℕ, Memℓp (fun n => deningerRapidWeight 𝕜 k n * a n) 2}
  add_mem' := by
    intro a b ha hb k
    have hfun : (fun n => deningerRapidWeight 𝕜 k n * (a + b) n)
        = (fun n => deningerRapidWeight 𝕜 k n * a n)
          + fun n => deningerRapidWeight 𝕜 k n * b n := by
      funext n
      simp [mul_add]
    rw [hfun]
    exact (ha k).add (hb k)
  zero_mem' := by
    intro k
    have hfun : (fun n => deningerRapidWeight 𝕜 k n * (0 : ℕ → 𝕜) n) = 0 := by
      funext n
      simp
    rw [hfun]
    exact zero_memℓp
  smul_mem' := by
    intro c a ha k
    have hfun : (fun n => deningerRapidWeight 𝕜 k n * (c • a) n)
        = c • fun n => deningerRapidWeight 𝕜 k n * a n := by
      funext n
      simp [mul_comm, mul_assoc]
    rw [hfun]
    exact (ha k).const_smul c

/-- The weighted coordinate map of the rapid sequence space into `ℓ²`. -/
noncomputable def deningerRapidMap (k : ℕ) :
    DeningerRapidCarrier 𝕜 →ₗ[𝕜] lp (fun _ : ℕ => 𝕜) 2 where
  toFun a := ⟨fun n => deningerRapidWeight 𝕜 k n * (a : ℕ → 𝕜) n, a.2 k⟩
  map_add' a b := by
    refine Subtype.ext (funext fun n => ?_)
    simp only [lp.coeFn_add, Pi.add_apply, Submodule.coe_add]
    ring
  map_smul' c a := by
    refine Subtype.ext (funext fun n => ?_)
    simp only [lp.coeFn_smul, Pi.smul_apply, SetLike.val_smul, RingHom.id_apply,
      smul_eq_mul]
    ring

@[simp]
theorem deningerRapidMap_apply (k : ℕ) (a : DeningerRapidCarrier 𝕜) (n : ℕ) :
    (deningerRapidMap k a : ℕ → 𝕜) n = deningerRapidWeight 𝕜 k n * (a : ℕ → 𝕜) n := rfl

/-- **The weighted `ℓ²` seminorms of the rapid sequence space.** -/
noncomputable def deningerRapidSeminorm (k : ℕ) : Seminorm 𝕜 (DeningerRapidCarrier 𝕜) :=
  (normSeminorm 𝕜 (lp (fun _ : ℕ => 𝕜) 2)).comp (deningerRapidMap k)

theorem deningerRapidSeminorm_apply (k : ℕ) (a : DeningerRapidCarrier 𝕜) :
    deningerRapidSeminorm k a = ‖deningerRapidMap k a‖ := rfl

/-- **Each weighted seminorm is Hilbertian**, being the norm of the weighted coordinate map. -/
theorem deningerRapidSeminorm_hilbertian (k : ℕ) :
    DeningerIsHilbertianSeminorm (deningerRapidSeminorm (𝕜 := 𝕜) k) :=
  ⟨ℕ, deningerRapidMap k, fun _ => rfl⟩

/-- **The coordinate bound**: every weighted coordinate is bounded by the corresponding
seminorm. -/
theorem deningerRapidWeight_norm_mul_le (k n : ℕ) (a : DeningerRapidCarrier 𝕜) :
    ((n : ℝ) + 1) ^ k * ‖(a : ℕ → 𝕜) n‖ ≤ deningerRapidSeminorm k a := by
  have hle := lp.norm_apply_le_norm (p := 2) (by norm_num) (deningerRapidMap k a) n
  rw [deningerRapidMap_apply, norm_mul, deningerRapidWeight_norm] at hle
  exact hle

/-- **The weighted seminorms increase with the weight.** -/
theorem deningerRapidSeminorm_le {k l : ℕ} (hkl : k ≤ l) (a : DeningerRapidCarrier 𝕜) :
    deningerRapidSeminorm k a ≤ deningerRapidSeminorm l a := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  refine lp.norm_le_of_forall_sum_le hp (norm_nonneg (deningerRapidMap l a)) fun s => ?_
  refine le_trans (Finset.sum_le_sum fun n _ => ?_)
    (lp.sum_rpow_le_norm_rpow hp (deningerRapidMap l a) s)
  have hcoord : ‖(deningerRapidMap k a : ℕ → 𝕜) n‖ ≤ ‖(deningerRapidMap l a : ℕ → 𝕜) n‖ := by
    rw [deningerRapidMap_apply, deningerRapidMap_apply, norm_mul, norm_mul,
      deningerRapidWeight_norm, deningerRapidWeight_norm]
    refine mul_le_mul_of_nonneg_right (pow_le_pow_right₀ ?_ hkl) (norm_nonneg _)
    · linarith [Nat.cast_nonneg (α := ℝ) n]
  exact Real.rpow_le_rpow (norm_nonneg _) hcoord hp.le

/-- The standard basis vector of the rapid sequence space. -/
noncomputable def deningerRapidBasis (𝕜 : Type*) [RCLike 𝕜] (n : ℕ) :
    DeningerRapidCarrier 𝕜 :=
  ⟨Pi.single n 1, fun k => by
    have hfun : (fun m => deningerRapidWeight 𝕜 k m * (Pi.single n (1 : 𝕜) : ℕ → 𝕜) m)
        = (Pi.single n (deningerRapidWeight 𝕜 k n) : ℕ → 𝕜) := by
      funext m
      by_cases h : m = n
      · subst h
        simp
      · simp [Pi.single_eq_of_ne h]
    rw [hfun]
    refine memℓp_gen (summable_of_ne_finset_zero (s := {n}) ?_)
    intro m hm
    have hmn : m ≠ n := by simpa using hm
    simp [Pi.single_eq_of_ne hmn]⟩

@[simp]
theorem deningerRapidBasis_coe (n : ℕ) :
    ((deningerRapidBasis 𝕜 n : DeningerRapidCarrier 𝕜) : ℕ → 𝕜) = Pi.single n 1 := rfl

theorem deningerRapidMap_basis (k n : ℕ) :
    deningerRapidMap k (deningerRapidBasis 𝕜 n)
      = lp.single 2 n (deningerRapidWeight 𝕜 k n) := by
  refine Subtype.ext (funext fun m => ?_)
  rw [lp.single_apply]
  show deningerRapidWeight 𝕜 k m * (Pi.single n (1 : 𝕜) : ℕ → 𝕜) m
    = (Pi.single n (deningerRapidWeight 𝕜 k n) : ℕ → 𝕜) m
  by_cases h : m = n
  · subst h
    simp
  · simp [Pi.single_eq_of_ne h]

/-- **The basis vectors have weighted norm exactly `(n+1)^k`.** -/
theorem deningerRapidSeminorm_basis (k n : ℕ) :
    deningerRapidSeminorm k (deningerRapidBasis 𝕜 n) = ((n : ℝ) + 1) ^ k := by
  rw [deningerRapidSeminorm_apply, deningerRapidMap_basis,
    lp.norm_single (by norm_num), deningerRapidWeight_norm]

end RapidSequences

end RHTower
