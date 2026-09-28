import GaloisForLFunctions.RHTower.PhysicalOrdinateExactExtractor
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# The rigged critical recovery

`H_{-a}` is the completion of finitely supported sequences under `‖f‖²_{-a} = Σ |f(n)|² n^{-2a}`;
in its isometric `ℓ²` coordinates `f̃(n) = n^{-a} f(n)`.  Remove the divergent normalisation:
`z_{σ,γ}(n) = μ(n) n^{-σ/2} n^{iγ}` **(11)**, i.e. `z̃_{σ,γ}(n) = n^{-a} μ(n) n^{-σ/2} n^{iγ}`.

* For `a > 0`, `z̃_{σ,γ} → z̃_{1,γ}` in `ℓ²` as `σ ↓ 1`; at `a = 0` there is no critical vector,
  since `Σ μ(n)²/n = ∞`.
* The prime multipliers `B_{σ,β}` **(12)**, in isometric coordinates
  `-log p · p^{a + (σ-1)/2} (p^{-β} - p^{β-1})`, are bounded when `a + (σ-1)/2 < κ = min(β, 1-β)`,
  with norm the supremum of the multiplier, satisfy `B_{σ,β} z̃_{σ,γ} = v_{β,γ}` at every height,
  and converge in operator norm to `B_{1,β}`, which lands `z̃_{1,γ}` on `v_{β,γ}`.
* **Sharp window.**  A bounded `B : H_{-a} → ℓ²(P)` with `B z̃_{1,γ} = v_{β,γ}` on a nonempty open
  interval agrees with `B_{1,β}` on the squarefree coordinates, so `‖B‖ ≥ log p · p^a |p^{-β} - p^{β-1}|`
  for every prime; such a `B` exists exactly when `a < κ`.
-/

noncomputable section
set_option autoImplicit false

open Complex Filter Topology Set

namespace RHTower

open GaloisForLFunctions.HTGeometry

local notation "ℓ²ℕ" => lp (fun _ : ℕ => ℂ) 2
local notation "ℓ²P" => lp (fun _ : Nat.Primes => ℂ) 2

/-! ### Prime diagonal operators `ℓ²(ℕ) → ℓ²(P)` -/

theorem memℓp_primeDiag {m : ℕ → ℂ} {C : ℝ} (hC : ∀ p : Nat.Primes, ‖m p‖ ≤ C) (f : ℓ²ℕ) :
    Memℓp (fun p : Nat.Primes => m p * (f : ℕ → ℂ) p) 2 := by
  refine HilbertSchmidt.memℓp_of_sq ?_
  have hf : Summable fun p : Nat.Primes => ‖(f : ℕ → ℂ) p‖ ^ 2 :=
    (summable_norm_sq_lp f).comp_injective Subtype.val_injective
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun p => ?_) (hf.mul_left (C ^ 2))
  rw [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hC p) 2) (sq_nonneg _)

/-- The prime diagonal operator `(D f)(p) = m(p) f(p)`. -/
def primeDiagOp (m : ℕ → ℂ) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ p : Nat.Primes, ‖m p‖ ≤ C) :
    ℓ²ℕ →L[ℂ] ℓ²P :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨_, memℓp_primeDiag hC f⟩
      map_add' := fun f g => by
        ext p
        change m p * ((f : ℕ → ℂ) p + (g : ℕ → ℂ) p) = m p * (f : ℕ → ℂ) p + m p * (g : ℕ → ℂ) p
        ring
      map_smul' := fun c f => by
        ext p
        change m p * (c * (f : ℕ → ℂ) p) = c * (m p * (f : ℕ → ℂ) p)
        ring }
    C fun f => by
      have hf : Summable fun p : Nat.Primes => ‖(f : ℕ → ℂ) p‖ ^ 2 :=
        (summable_norm_sq_lp f).comp_injective Subtype.val_injective
      have h2 : ‖(⟨_, memℓp_primeDiag hC f⟩ : ℓ²P)‖ ^ 2 ≤ (C * ‖f‖) ^ 2 := by
        rw [HilbertSchmidt.lp_norm_sq_eq, mul_pow, HilbertSchmidt.lp_norm_sq_eq]
        calc ∑' p : Nat.Primes, ‖m p * (f : ℕ → ℂ) p‖ ^ 2
            ≤ ∑' p : Nat.Primes, C ^ 2 * ‖(f : ℕ → ℂ) p‖ ^ 2 := by
              refine Summable.tsum_le_tsum (fun p => ?_)
                (summable_norm_sq_lp (⟨_, memℓp_primeDiag hC f⟩ : ℓ²P)) (hf.mul_left _)
              rw [norm_mul, mul_pow]
              exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hC p) 2)
                (sq_nonneg _)
          _ = C ^ 2 * ∑' p : Nat.Primes, ‖(f : ℕ → ℂ) p‖ ^ 2 := tsum_mul_left
          _ ≤ C ^ 2 * ∑' n : ℕ, ‖(f : ℕ → ℂ) n‖ ^ 2 := by
              gcongr
              exact hf.tsum_le_tsum_of_inj Subtype.val Subtype.val_injective
                (fun _ _ => by positivity) (fun _ => le_rfl) (summable_norm_sq_lp f)
      exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC0 (norm_nonneg f))).mp h2

theorem primeDiagOp_apply (m : ℕ → ℂ) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ p : Nat.Primes, ‖m p‖ ≤ C)
    (f : ℓ²ℕ) (p : Nat.Primes) :
    (primeDiagOp m hC0 hC f : Nat.Primes → ℂ) p = m p * (f : ℕ → ℂ) p := rfl

theorem norm_primeDiagOp_le (m : ℕ → ℂ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ p : Nat.Primes, ‖m p‖ ≤ C) : ‖primeDiagOp m hC0 hC‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC0 _

theorem norm_le_norm_primeDiagOp (m : ℕ → ℂ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ p : Nat.Primes, ‖m p‖ ≤ C) (p : Nat.Primes) : ‖m p‖ ≤ ‖primeDiagOp m hC0 hC‖ := by
  set e : ℓ²ℕ := lp.single (E := fun _ : ℕ => ℂ) 2 (p : ℕ) 1 with he
  have he1 : ‖e‖ = 1 := by rw [he, lp.norm_single (by norm_num)]; simp
  have h1 := lp.norm_apply_le_norm (E := fun _ : Nat.Primes => ℂ) (p := 2) two_ne_zero
    (primeDiagOp m hC0 hC e) p
  have h2 := (primeDiagOp m hC0 hC).le_opNorm e
  rw [he1, mul_one] at h2
  rw [primeDiagOp_apply, he, lp.single_apply_self, mul_one] at h1
  exact h1.trans h2

/-- The norm of a prime diagonal operator is the supremum of its multiplier. -/
theorem norm_primeDiagOp (m : ℕ → ℂ) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ p : Nat.Primes, ‖m p‖ ≤ C) :
    ‖primeDiagOp m hC0 hC‖ = ⨆ p : Nat.Primes, ‖m p‖ := by
  have hb : BddAbove (range fun p : Nat.Primes => ‖m p‖) := ⟨C, by rintro _ ⟨p, rfl⟩; exact hC p⟩
  refine le_antisymm ?_ (ciSup_le fun p => norm_le_norm_primeDiagOp m hC0 hC p)
  refine LinearMap.mkContinuous_norm_le _ ((norm_nonneg _).trans (le_ciSup hb ⟨2, Nat.prime_two⟩))
    fun f => ?_
  exact ContinuousLinearMap.le_of_opNorm_le _
    (norm_primeDiagOp_le m ((norm_nonneg _).trans (le_ciSup hb ⟨2, Nat.prime_two⟩))
      (fun p => le_ciSup hb p)) f |>.trans_eq' rfl

theorem primeDiagOp_sub (m m' : ℕ → ℂ) {C C' D : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ p : Nat.Primes, ‖m p‖ ≤ C) (hC0' : 0 ≤ C') (hC' : ∀ p : Nat.Primes, ‖m' p‖ ≤ C')
    (hD0 : 0 ≤ D) (hD : ∀ p : Nat.Primes, ‖m p - m' p‖ ≤ D) :
    primeDiagOp m hC0 hC - primeDiagOp m' hC0' hC' = primeDiagOp (fun n => m n - m' n) hD0 hD := by
  refine ContinuousLinearMap.ext fun f => ?_
  ext p
  change m p * (f : ℕ → ℂ) p - m' p * (f : ℕ → ℂ) p = (m p - m' p) * (f : ℕ → ℂ) p
  ring

/-! ### The rigged source -/

/-- The rigged source `z̃_{σ,γ}(n) = n^{-a} μ(n) n^{-σ/2} n^{iγ}` in isometric coordinates. -/
def riggedCoord (a σ γ : ℝ) (n : ℕ) : ℂ :=
  ((ArithmeticFunction.moebius n : ℤ) : ℂ) * (((n : ℝ) ^ (-(a + σ / 2)) : ℝ) : ℂ) *
    GaloisForLFunctions.expChar (Real.log n) γ

theorem norm_riggedCoord_sq_le (a σ γ : ℝ) (n : ℕ) :
    ‖riggedCoord a σ γ n‖ ^ 2 ≤ ((n : ℝ) ^ (-(a + σ / 2))) ^ 2 := by
  rw [riggedCoord, norm_mul, norm_mul, GaloisForLFunctions.norm_expChar, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_pow]
  have hμ : ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have : ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ^ 2 ≤ 1 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hμ 2; simpa using this
  nlinarith [sq_nonneg ((n : ℝ) ^ (-(a + σ / 2)))]

theorem summable_rpow_sq {s : ℝ} (hs : 1 < s) :
    Summable fun n : ℕ => ((n : ℝ) ^ (-(s / 2))) ^ 2 := by
  refine (Real.summable_nat_rpow_inv.mpr hs).congr fun n => ?_
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _),
    show -(s / 2) * ((2 : ℕ) : ℝ) = -s by push_cast; ring, Real.rpow_neg (Nat.cast_nonneg _)]

theorem memℓp_riggedCoord {a σ : ℝ} (h : 1 < 2 * a + σ) (γ : ℝ) :
    Memℓp (riggedCoord a σ γ) 2 := by
  refine HilbertSchmidt.memℓp_of_sq (Summable.of_nonneg_of_le (fun _ => by positivity)
    (norm_riggedCoord_sq_le a σ γ) ?_)
  have := summable_rpow_sq h
  refine this.congr fun n => ?_
  congr 2
  ring

/-- `z̃_{σ,γ}` for `σ ≥ 1` (zero otherwise), `a > 0`. -/
def riggedSource (a σ γ : ℝ) : ℓ²ℕ :=
  if h : 1 < 2 * a + σ then ⟨riggedCoord a σ γ, memℓp_riggedCoord h γ⟩ else 0

theorem riggedSource_apply {a σ : ℝ} (h : 1 < 2 * a + σ) (γ : ℝ) (n : ℕ) :
    (riggedSource a σ γ : ℕ → ℂ) n = riggedCoord a σ γ n := by
  rw [riggedSource, dif_pos h]

/-- **(11)** `z̃_{σ,γ} → z̃_{1,γ}` in `ℓ²` as `σ ↓ 1`, for every `a > 0`. -/
theorem tendsto_riggedSource {a : ℝ} (ha : 0 < a) (γ : ℝ) :
    Tendsto (fun σ => riggedSource a σ γ) (𝓝[>] 1) (𝓝 (riggedSource a 1 γ)) := by
  have h1 : 1 < 2 * a + 1 := by linarith
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : Tendsto (fun σ => ‖riggedSource a σ γ - riggedSource a 1 γ‖ ^ 2) (𝓝[>] 1) (𝓝 0) := by
    have e : ∀ᶠ σ in 𝓝[>] (1 : ℝ), ‖riggedSource a σ γ - riggedSource a 1 γ‖ ^ 2 =
        ∑' n, ‖riggedCoord a σ γ n - riggedCoord a 1 γ n‖ ^ 2 := by
      filter_upwards [self_mem_nhdsWithin] with σ hσ
      have hσ' : 1 < 2 * a + σ := by linarith [show (1 : ℝ) < σ from hσ]
      rw [HilbertSchmidt.lp_norm_sq_eq]
      refine tsum_congr fun n => ?_
      rw [lp.coeFn_sub, Pi.sub_apply, riggedSource_apply hσ', riggedSource_apply h1]
    refine Tendsto.congr' (EventuallyEq.symm e) ?_
    have hbound : Summable fun n : ℕ => 4 * ((n : ℝ) ^ (-((2 * a + 1) / 2))) ^ 2 :=
      (summable_rpow_sq h1).mul_left 4
    have h := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[>] (1 : ℝ))
      (f := fun σ n => ‖riggedCoord a σ γ n - riggedCoord a 1 γ n‖ ^ 2) (g := fun _ => 0)
      (bound := fun n => 4 * ((n : ℝ) ^ (-((2 * a + 1) / 2))) ^ 2) hbound (fun n => ?_) ?_
    · simpa using h
    · have hc : ContinuousAt (fun σ : ℝ => ‖riggedCoord a σ γ n - riggedCoord a 1 γ n‖ ^ 2) 1 := by
        unfold riggedCoord
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · subst h0; simp; exact continuousAt_const
        · have hn0 : (0 : ℝ) < n := by exact_mod_cast hpos
          have : ContinuousAt (fun σ : ℝ => (n : ℝ) ^ (-(a + σ / 2))) 1 :=
            (Real.continuousAt_const_rpow hn0.ne').comp (by fun_prop)
          exact (((continuous_const.continuousAt.mul (Complex.continuous_ofReal.continuousAt.comp
            this)).mul continuous_const.continuousAt).sub continuousAt_const).norm.pow 2
      have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (1 : ℝ)))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with σ hσ n
      have hσ1 : (1 : ℝ) ≤ σ := le_of_lt hσ
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hmono : ∀ s, 1 ≤ s → ‖riggedCoord a s γ n‖ ≤ (n : ℝ) ^ (-((2 * a + 1) / 2)) := by
        intro s hs
        have h := norm_riggedCoord_sq_le a s γ n
        have h' : ‖riggedCoord a s γ n‖ ≤ (n : ℝ) ^ (-(a + s / 2)) :=
          (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp h
        refine h'.trans ?_
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · subst h0
          simp only [Nat.cast_zero]
          rw [Real.zero_rpow (ne_of_lt (by linarith)), Real.zero_rpow (ne_of_lt (by linarith))]
        · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hpos) (by linarith)
      have := norm_sub_le (riggedCoord a σ γ n) (riggedCoord a 1 γ n)
      have h2 := hmono σ hσ1
      have h3 := hmono 1 le_rfl
      nlinarith [norm_nonneg (riggedCoord a σ γ n - riggedCoord a 1 γ n)]
  have h := (Real.continuous_sqrt.tendsto 0).comp hsq
  simp only [Real.sqrt_zero, Function.comp_def] at h
  refine h.congr fun σ => ?_
  rw [Real.sqrt_sq (norm_nonneg _)]

/-- **No critical vector at `a = 0`**: `n ↦ μ(n) n^{-1/2}` is not square summable. -/
theorem not_memℓp_critical_unrigged (γ : ℝ) : ¬ Memℓp (riggedCoord 0 1 γ) 2 := by
  intro h
  have hsum : Summable fun n => ‖riggedCoord 0 1 γ n‖ ^ 2 := by
    have := h.summable (show 0 < (2 : ENNReal).toReal by norm_num)
    simpa [show ((2 : ENNReal).toReal) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] using this
  apply not_summable_one_div_on_primes
  refine hsum.of_nonneg_of_le (fun n => by
    simp only [Set.indicator]; split_ifs <;> positivity) (fun n => ?_)
  simp only [Set.indicator, mem_setOf_eq]
  split_ifs with hp
  · rw [riggedCoord, norm_mul, norm_mul, GaloisForLFunctions.norm_expChar, mul_one,
      ArithmeticFunction.moebius_apply_prime hp, Complex.norm_real, Real.norm_eq_abs]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hp.pos
    rw [abs_of_nonneg (by positivity)]
    simp only [zero_add, Int.cast_neg, Int.cast_one, norm_neg, norm_one, one_mul]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le,
      show -(1 / 2 : ℝ) * ((2 : ℕ) : ℝ) = -1 by push_cast; ring, Real.rpow_neg_one, one_div]
  · positivity

/-! ### The rigged extractor (12) -/

/-- The rigged multiplier `-log p · p^{a + (σ-1)/2} (p^{-β} - p^{β-1})`. -/
def riggedMultiplier (a σ β : ℝ) (n : ℕ) : ℂ :=
  ((-(Real.log n * (n : ℝ) ^ (a + (σ - 1) / 2) * ((n : ℝ) ^ (-β) - (n : ℝ) ^ (β - 1))) : ℝ) : ℂ)

theorem norm_riggedMultiplier (a σ β : ℝ) (n : ℕ) :
    ‖riggedMultiplier a σ β n‖ = seamLogProfile (2 * a + σ) β n := by
  rw [riggedMultiplier, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_mul, abs_mul,
    abs_of_nonneg (Real.log_natCast_nonneg n), abs_of_nonneg (by positivity), seamLogProfile]
  congr 3; ring

theorem norm_riggedMultiplier_le {a σ β : ℝ} (hw : a + (σ - 1) / 2 < min β (1 - β)) (p : ℕ) :
    ‖riggedMultiplier a σ β p‖ ≤ 2 / (min β (1 - β) - (a + (σ - 1) / 2)) := by
  rw [norm_riggedMultiplier]
  have h := seamLogProfile_bound (σ := 2 * a + σ) (β := β) (by linarith) p
  convert h using 2; ring

theorem riggedBound_nonneg {a σ β : ℝ} (hw : a + (σ - 1) / 2 < min β (1 - β)) :
    0 ≤ 2 / (min β (1 - β) - (a + (σ - 1) / 2)) :=
  div_nonneg (by norm_num) (by linarith)

/-- The rigged extractor `B_{σ,β}` on `H_{-a}` (isometric coordinates). -/
def riggedOp (a σ β : ℝ) (hw : a + (σ - 1) / 2 < min β (1 - β)) : ℓ²ℕ →L[ℂ] ℓ²P :=
  primeDiagOp (riggedMultiplier a σ β) (riggedBound_nonneg hw) (fun p => norm_riggedMultiplier_le hw p)

/-- **(12)** `‖B_{σ,β}‖ = sup_p log p · p^{a+(σ-1)/2} |p^{-β} - p^{β-1}|`. -/
theorem norm_riggedOp {a σ β : ℝ} (hw : a + (σ - 1) / 2 < min β (1 - β)) :
    ‖riggedOp a σ β hw‖ = ⨆ p : Nat.Primes, seamLogProfile (2 * a + σ) β p := by
  rw [riggedOp, norm_primeDiagOp]
  exact iSup_congr fun p => norm_riggedMultiplier a σ β p

theorem riggedMultiplier_mul_riggedCoord (a σ β γ : ℝ) (p : Nat.Primes) :
    riggedMultiplier a σ β p * riggedCoord a σ γ p =
      (seamAmplitude β p : ℂ) * GaloisForLFunctions.expChar (Real.log p) γ := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hpow : (p : ℝ) ^ (a + (σ - 1) / 2) * (p : ℝ) ^ (-(a + σ / 2)) = 1 / Real.sqrt p := by
    rw [← Real.rpow_add hp0, Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg hp0.le]; ring_nf
  rw [riggedMultiplier, riggedCoord, ArithmeticFunction.moebius_apply_prime p.2, seamAmplitude]
  have e : (-(Real.log p * (p : ℝ) ^ (a + (σ - 1) / 2) * ((p : ℝ) ^ (-β) - (p : ℝ) ^ (β - 1)))) *
      (-1 * (p : ℝ) ^ (-(a + σ / 2))) =
      Real.log p / Real.sqrt p * ((p : ℝ) ^ (-β) - (p : ℝ) ^ (β - 1)) := by
    rw [show (-(Real.log p * (p : ℝ) ^ (a + (σ - 1) / 2) * ((p : ℝ) ^ (-β) - (p : ℝ) ^ (β - 1)))) *
      (-1 * (p : ℝ) ^ (-(a + σ / 2))) = Real.log p * ((p : ℝ) ^ (a + (σ - 1) / 2) *
        (p : ℝ) ^ (-(a + σ / 2))) * ((p : ℝ) ^ (-β) - (p : ℝ) ^ (β - 1)) by ring, hpow]
    ring
  rw [← e]
  push_cast
  ring

/-- **(12)** `B_{σ,β} z̃_{σ,γ} = v_{β,γ}` at every height. -/
theorem riggedOp_riggedSource {a σ β : ℝ} (hβ : β ∈ Ioo 0 1)
    (hw : a + (σ - 1) / 2 < min β (1 - β)) (h : 1 < 2 * a + σ) (γ : ℝ) :
    riggedOp a σ β hw (riggedSource a σ γ) = seamVector β hβ γ := by
  ext p
  rw [riggedOp, primeDiagOp_apply, riggedSource_apply h, riggedMultiplier_mul_riggedCoord,
    seamVector_apply]

/-- **(12)** `B_{σ,β} → B_{1,β}` in operator norm as `σ ↓ 1`. -/
theorem tendsto_riggedOp {a β : ℝ} (hw : a < min β (1 - β)) :
    Tendsto (fun σ => if h : a + (σ - 1) / 2 < min β (1 - β) then riggedOp a σ β h else 0)
      (𝓝[>] 1) (𝓝 (riggedOp a 1 β (by simpa using hw))) := by
  set κ := min β (1 - β) with hκ
  set δ : ℝ := (κ - a) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hwin : ∀ᶠ σ in 𝓝[>] (1 : ℝ), 1 < σ ∧ (σ - 1) / 2 < δ := by
    have h1 : Iio (1 + 2 * δ) ∈ 𝓝[>] (1 : ℝ) := nhdsWithin_le_nhds (Iio_mem_nhds (by linarith))
    filter_upwards [self_mem_nhdsWithin, h1] with σ hσ h2
    exact ⟨hσ, by simp only [mem_Iio] at h2; linarith⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  -- uniform smallness of the multiplier difference
  have hdiff : ∀ ε > 0, ∀ᶠ σ in 𝓝[>] (1 : ℝ), ∀ p : Nat.Primes,
      ‖riggedMultiplier a σ β p - riggedMultiplier a 1 β p‖ ≤ ε := by
    intro ε hε
    set P : ℝ := max 1 ((16 / (δ * ε)) ^ (2 / δ)) with hP
    have htail : ∀ x : ℝ, P ≤ x → 4 * (Real.log x * x ^ (-δ)) ≤ ε := by
      intro x hx
      have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hx
      have hx0 : 0 < x := by linarith
      have hlog : Real.log x ≤ x ^ (δ / 2) / (δ / 2) := Real.log_le_rpow_div hx0.le (by positivity)
      have hbig : (16 / (δ * ε)) ^ (2 / δ) ≤ x := le_trans (le_max_right _ _) hx
      have h1 : 16 / (δ * ε) ≤ x ^ (δ / 2) := by
        calc 16 / (δ * ε) = ((16 / (δ * ε)) ^ (2 / δ)) ^ (δ / 2) := by
              rw [← Real.rpow_mul (by positivity), show 2 / δ * (δ / 2) = 1 by field_simp,
                Real.rpow_one]
          _ ≤ x ^ (δ / 2) := Real.rpow_le_rpow (by positivity) hbig (by positivity)
      have hpos : 0 < x ^ (δ / 2) := Real.rpow_pos_of_pos hx0 _
      have h2 : x ^ (-(δ / 2)) ≤ δ * ε / 16 := by
        rw [Real.rpow_neg hx0.le, inv_le_comm₀ hpos (by positivity)]
        calc (δ * ε / 16)⁻¹ = 16 / (δ * ε) := by field_simp
          _ ≤ _ := h1
      calc 4 * (Real.log x * x ^ (-δ)) ≤ 4 * (x ^ (δ / 2) / (δ / 2) * x ^ (-δ)) := by gcongr
        _ = 8 / δ * x ^ (-(δ / 2)) := by
            rw [div_mul_eq_mul_div, ← Real.rpow_add hx0]; field_simp; ring_nf
        _ ≤ 8 / δ * (δ * ε / 16) := by gcongr
        _ ≤ ε := by field_simp; nlinarith
    have hhead : Tendsto (fun σ : ℝ => P ^ ((σ - 1) / 2) - 1) (𝓝[>] 1) (𝓝 0) := by
      have hc : ContinuousAt (fun σ : ℝ => P ^ ((σ - 1) / 2) - 1) 1 :=
        ((Real.continuousAt_const_rpow (by positivity)).comp (by fun_prop)).sub continuousAt_const
      have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (1 : ℝ)))
      simpa using this
    have hC1 : 0 ≤ ⨆ p : Nat.Primes, seamLogProfile (2 * a + 1) β p :=
      (seamLogProfile_nonneg _ _ 2).trans (le_ciSup (bddAbove_seamLogProfile (by linarith))
        (⟨2, Nat.prime_two⟩ : Nat.Primes))
    filter_upwards [hwin, hhead.eventually (ge_mem_nhds (show (0 : ℝ) < ε /
      ((⨆ p : Nat.Primes, seamLogProfile (2 * a + 1) β p) + 1) by positivity))] with σ hσ hh p
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast p.2.one_le
    have hp0 : (0 : ℝ) < p := by linarith
    have hfac : riggedMultiplier a σ β p - riggedMultiplier a 1 β p =
        riggedMultiplier a 1 β p * (((p : ℝ) ^ ((σ - 1) / 2) - 1 : ℝ) : ℂ) := by
      have hreal : -(Real.log p * (p : ℝ) ^ (a + (σ - 1) / 2) * ((p : ℝ) ^ (-β) - (p : ℝ) ^ (β - 1))) -
          -(Real.log p * (p : ℝ) ^ (a + (1 - 1) / 2) * ((p : ℝ) ^ (-β) - (p : ℝ) ^ (β - 1))) =
          -(Real.log p * (p : ℝ) ^ (a + (1 - 1) / 2) * ((p : ℝ) ^ (-β) - (p : ℝ) ^ (β - 1))) *
            ((p : ℝ) ^ ((σ - 1) / 2) - 1) := by
        rw [show a + (1 - 1) / 2 = a by ring, Real.rpow_add hp0]; ring
      unfold riggedMultiplier
      rw [← Complex.ofReal_sub, hreal, Complex.ofReal_mul]
    rw [hfac, norm_mul, norm_riggedMultiplier, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [Real.one_le_rpow hp1 (by linarith [hσ.1] : 0 ≤ (σ - 1) / 2)])]
    by_cases hpP : P ≤ (p : ℝ)
    · have h1 : seamLogProfile (2 * a + 1) β p * ((p : ℝ) ^ ((σ - 1) / 2) - 1) ≤
          seamLogProfile (2 * a + σ) β p := by
        rw [seamLogProfile_eq_mul (2 * a + σ), seamLogProfile_eq_mul (2 * a + 1)]
        have h0 := seamLogProfile_nonneg 1 β p
        have : (p : ℝ) ^ ((2 * a + 1 - 1) / 2) * ((p : ℝ) ^ ((σ - 1) / 2) - 1) ≤
            (p : ℝ) ^ ((2 * a + σ - 1) / 2) := by
          rw [mul_sub, mul_one, ← Real.rpow_add hp0]
          have : 0 ≤ (p : ℝ) ^ ((2 * a + 1 - 1) / 2) := by positivity
          rw [show (2 * a + 1 - 1) / 2 + (σ - 1) / 2 = (2 * a + σ - 1) / 2 by ring]
          linarith
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left this h0
      refine h1.trans ?_
      refine (seamLogProfile_le (σ := 2 * a + σ) (β := β) p.2.one_le).trans ?_
      have hexp : (p : ℝ) ^ (-(κ - (2 * a + σ - 1) / 2)) ≤ (p : ℝ) ^ (-δ) :=
        Real.rpow_le_rpow_of_exponent_le hp1 (by rw [hδ]; linarith [hσ.2])
      have := htail p hpP
      have hlog := Real.log_nonneg hp1
      nlinarith [mul_le_mul_of_nonneg_left hexp hlog]
    · push Not at hpP
      have hP1 : (p : ℝ) ^ ((σ - 1) / 2) ≤ P ^ ((σ - 1) / 2) :=
        Real.rpow_le_rpow hp0.le hpP.le (by linarith [hσ.1])
      have hprof : seamLogProfile (2 * a + 1) β p ≤ ⨆ p : Nat.Primes, seamLogProfile (2 * a + 1) β p :=
        le_ciSup (bddAbove_seamLogProfile (by linarith)) p
      have hg : 0 ≤ (p : ℝ) ^ ((σ - 1) / 2) - 1 := by
        linarith [Real.one_le_rpow hp1 (by linarith [hσ.1] : 0 ≤ (σ - 1) / 2)]
      calc seamLogProfile (2 * a + 1) β p * ((p : ℝ) ^ ((σ - 1) / 2) - 1)
          ≤ (⨆ p : Nat.Primes, seamLogProfile (2 * a + 1) β p) * (P ^ ((σ - 1) / 2) - 1) := by
            gcongr
        _ ≤ (⨆ p : Nat.Primes, seamLogProfile (2 * a + 1) β p) *
            (ε / ((⨆ p : Nat.Primes, seamLogProfile (2 * a + 1) β p) + 1)) := by gcongr
        _ ≤ ε := by
            rw [mul_div_assoc']
            rw [div_le_iff₀ (by positivity)]
            nlinarith
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hwin, hdiff (ε / 2) (by positivity)] with σ hσ hd
  have hwσ : a + (σ - 1) / 2 < κ := by rw [hδ] at hσ; linarith [hσ.2]
  rw [dif_pos hwσ, dist_zero_right, norm_norm, riggedOp, riggedOp,
    primeDiagOp_sub _ _ _ _ _ _ (by positivity : (0 : ℝ) ≤ ε / 2) hd]
  exact lt_of_le_of_lt (norm_primeDiagOp_le _ _ _) (by linarith)

/-- `B_{1,β} z̃_{1,γ} = v_{β,γ}` for `0 < a < κ`. -/
theorem riggedOp_one_riggedSource {a β : ℝ} (hβ : β ∈ Ioo 0 1) (ha : 0 < a)
    (hw : a < min β (1 - β)) (γ : ℝ) :
    riggedOp a 1 β (by simpa using hw) (riggedSource a 1 γ) = seamVector β hβ γ :=
  riggedOp_riggedSource hβ _ (by linarith) γ

/-! ### The sharp window -/

/-- `sup_p s_p(s) < ∞` exactly when `s < 1 + 2 min(β, 1-β)` (`β ≠ 1/2`). -/
theorem bddAbove_seamLogProfile_iff {s β : ℝ} (hβ2 : β ≠ 1 / 2) :
    BddAbove (range fun p : Nat.Primes => seamLogProfile s β p) ↔ s < 1 + 2 * min β (1 - β) := by
  refine ⟨fun hb => ?_, bddAbove_seamLogProfile⟩
  by_contra hw
  push Not at hw
  obtain ⟨C, hC⟩ := hb
  set κ := min β (1 - β) with hκ
  set P₀ : ℝ := max (2 ^ (1 / (1 - 2 * κ))) (Real.exp (2 * |C| + 1)) with hP₀
  obtain ⟨p, hpP, hp⟩ := Nat.exists_infinite_primes (⌈P₀⌉₊ + 1)
  have hpP' : P₀ < p := by
    have := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hpP
    exact lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast this)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hmem := hC ⟨⟨p, hp⟩, rfl⟩
  simp only at hmem
  have hlow := half_rpow_neg_le_abs hβ2 (x := p) (le_trans (le_max_left _ _) hpP'.le)
  have hexp : 1 ≤ (p : ℝ) ^ ((s - 1) / 2 - κ) := Real.one_le_rpow hp1 (by linarith)
  have hlogbig : 2 * |C| + 1 < Real.log p := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    exact lt_of_le_of_lt (le_max_right _ _) hpP'
  have hlog0 : 0 ≤ Real.log p := Real.log_nonneg hp1
  have h1 : Real.log p / 2 ≤ seamLogProfile s β p := by
    have e : (p : ℝ) ^ ((s - 1) / 2) * ((p : ℝ) ^ (-κ) / 2) = (p : ℝ) ^ ((s - 1) / 2 - κ) / 2 := by
      rw [mul_div_assoc', ← Real.rpow_add hp0]; ring_nf
    unfold seamLogProfile
    calc Real.log p / 2 ≤ Real.log p * ((p : ℝ) ^ ((s - 1) / 2 - κ) / 2) := by nlinarith
      _ = Real.log p * ((p : ℝ) ^ ((s - 1) / 2) * ((p : ℝ) ^ (-κ) / 2)) := by rw [e]
      _ ≤ _ := by rw [← mul_assoc]; gcongr
  nlinarith [le_abs_self C]

/-- The rigged source coefficient `μ(n) n^{-(a+1/2)}` at `σ = 1`. -/
def riggedWeight (a : ℝ) (n : ℕ) : ℂ :=
  ((ArithmeticFunction.moebius n : ℤ) : ℂ) * (((n : ℝ) ^ (-(a + 1 / 2)) : ℝ) : ℂ)

theorem riggedCoord_one (a γ : ℝ) (n : ℕ) :
    riggedCoord a 1 γ n = riggedWeight a n * GaloisForLFunctions.expChar (Real.log n) γ := rfl

theorem riggedMultiplier_mul_riggedWeight (a β : ℝ) (p : Nat.Primes) :
    riggedMultiplier a 1 β p * riggedWeight a p = (seamAmplitude β p : ℂ) := by
  have h := riggedMultiplier_mul_riggedCoord a 1 β 0 p
  simp only [riggedCoord_one, GaloisForLFunctions.expChar, mul_zero, ofReal_zero, zero_mul,
    Complex.exp_zero, mul_one] at h
  exact h

theorem weightedAbsSummable_rigged_mul {a η : ℝ} (hη : η < a) {t : ℕ → ℂ}
    (ht : Summable fun n => ‖t n‖ ^ 2) :
    WeightedAbsSummable (fun n => riggedWeight a n * t n) η := by
  have hs : Summable fun n : ℕ => ((n : ℝ) ^ (-((1 + 2 * (a - η)) / 2))) ^ 2 :=
    summable_rpow_sq (by linarith)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) ((hs.add ht).div_const 2)
  rw [norm_mul]
  have hw : ‖riggedWeight a n‖ ≤ (n : ℝ) ^ (-(a + 1 / 2)) := by
    rw [riggedWeight, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hμ : ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have : 0 ≤ (n : ℝ) ^ (-(a + 1 / 2)) := by positivity
    nlinarith
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    have : ‖riggedWeight a 0‖ = 0 := by simp [riggedWeight]
    rw [this]; simp; positivity
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hpos
    have key : ‖riggedWeight a n‖ * (n : ℝ) ^ η ≤ (n : ℝ) ^ (-((1 + 2 * (a - η)) / 2)) := by
      calc ‖riggedWeight a n‖ * (n : ℝ) ^ η ≤ (n : ℝ) ^ (-(a + 1 / 2)) * (n : ℝ) ^ η := by gcongr
        _ = (n : ℝ) ^ (-((1 + 2 * (a - η)) / 2)) := by rw [← Real.rpow_add hn0]; ring_nf
    have : ‖riggedWeight a n‖ * ‖t n‖ * (n : ℝ) ^ η ≤
        (n : ℝ) ^ (-((1 + 2 * (a - η)) / 2)) * ‖t n‖ := by
      rw [mul_right_comm]; exact mul_le_mul_of_nonneg_right key (norm_nonneg _)
    refine this.trans ?_
    nlinarith [sq_nonneg ((n : ℝ) ^ (-((1 + 2 * (a - η)) / 2)) - ‖t n‖)]

/-- The `p`-coordinate of `B z̃_{1,γ}` is a Dirichlet readout. -/
theorem coord_rigged_eq_readout {a : ℝ} (ha : 0 < a) (B : ℓ²ℕ →L[ℂ] ℓ²P) (p : Nat.Primes)
    (γ : ℝ) : (B (riggedSource a 1 γ) : Nat.Primes → ℂ) p =
      dirichletReadout (fun n => riggedWeight a n * (B (lp.single 2 n 1) : Nat.Primes → ℂ) p) γ := by
  have hw := weightedAbsSummable_rigged_mul (η := 0) ha (summable_norm_sq_coord B p)
  rw [dirichletReadout_ofReal hw le_rfl, GaloisForLFunctions.expSeriesCarrier]
  have h := hasSum_coord B (riggedSource a 1 γ) p
  rw [← h.tsum_eq, h.summable.tsum_eq_zero_add]
  have h1 : 1 < 2 * a + 1 := by linarith
  simp only [riggedSource_apply h1, riggedCoord_one]
  have hw0 : riggedWeight a 0 = 0 := by simp [riggedWeight]
  rw [hw0, zero_mul, zero_mul, zero_add]
  refine tsum_congr fun m => ?_
  ring

/-- **Rigidity on `H_{-a}`.**  A bounded `B` with `B z̃_{1,γ} = v_{β,γ}` on a nonempty open interval
agrees with `B_{1,β}` on every squarefree coordinate. -/
theorem coord_eq_of_rigged_landing {a β : ℝ} (ha : 0 < a) (hβ : β ∈ Ioo 0 1)
    (B : ℓ²ℕ →L[ℂ] ℓ²P) {c d : ℝ} (hcd : c < d)
    (hB : ∀ γ ∈ Ioo c d, B (riggedSource a 1 γ) = seamVector β hβ γ) (p : Nat.Primes)
    {n : ℕ} (hn : Squarefree n) :
    (B (lp.single 2 n 1) : Nat.Primes → ℂ) p = if n = p then riggedMultiplier a 1 β p else 0 := by
  set η : ℝ := a / 2 with hηdef
  have hη : 0 < η := by positivity
  have hw := weightedAbsSummable_rigged_mul (a := a) (η := η) (by rw [hηdef]; linarith)
    (summable_norm_sq_coord B p)
  have hinterval : ∀ t ∈ Ioo c d, dirichletReadout
      (fun n => riggedWeight a n * (B (lp.single 2 n 1) : Nat.Primes → ℂ) p) t =
        seamCoordEntire β p t := by
    intro t ht
    rw [← coord_rigged_eq_readout ha B p t, hB t ht, seamVector_apply, seamCoordEntire_ofReal]
  have hline : ∀ t : ℝ, dirichletReadout
      (fun n => riggedWeight a n * (B (lp.single 2 n 1) : Nat.Primes → ℂ) p) t =
        dirichletReadout (seamCoeffSeq β p) t := by
    intro t
    rw [dirichletReadout_seamCoeffSeq p.2.pos]
    exact dirichletReadout_eq_of_eqOn_Ioo hw hη (differentiable_seamCoordEntire β p) hcd
      hinterval (by simp; linarith)
  have hn0 : 0 < n := Nat.pos_of_ne_zero fun h => by subst h; exact not_squarefree_zero hn
  have hcoef := coeff_eq_of_dirichletReadout_eq hw (weightedAbsSummable_seamCoeffSeq β p η) hη.le
    hline hn0
  simp only [seamCoeffSeq] at hcoef
  have hwn : riggedWeight a n ≠ 0 := by
    have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
    refine mul_ne_zero ?_ (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hn0' _).ne')
    rw [ArithmeticFunction.moebius_apply_of_squarefree hn]
    simp
  split_ifs at hcoef ⊢ with hnp
  · subst hnp
    have := riggedMultiplier_mul_riggedWeight a β p
    rw [← this, mul_comm (riggedMultiplier a 1 β p)] at hcoef
    exact mul_left_cancel₀ hwn hcoef
  · exact (mul_eq_zero.mp hcoef).resolve_left hwn

theorem norm_riggedMultiplier_le_of_rigged_landing {a β : ℝ} (ha : 0 < a) (hβ : β ∈ Ioo 0 1)
    (B : ℓ²ℕ →L[ℂ] ℓ²P) {c d : ℝ} (hcd : c < d)
    (hB : ∀ γ ∈ Ioo c d, B (riggedSource a 1 γ) = seamVector β hβ γ) (p : Nat.Primes) :
    ‖riggedMultiplier a 1 β p‖ ≤ ‖B‖ := by
  have h := coord_eq_of_rigged_landing ha hβ B hcd hB p p.2.squarefree
  rw [if_pos rfl] at h
  set e : ℓ²ℕ := lp.single (E := fun _ : ℕ => ℂ) 2 (p : ℕ) 1 with he
  have he1 : ‖e‖ = 1 := by rw [he, lp.norm_single (by norm_num)]; simp
  have h1 := lp.norm_apply_le_norm (E := fun _ : Nat.Primes => ℂ) (p := 2) two_ne_zero (B e) p
  have h2 := B.le_opNorm e
  rw [he1, mul_one] at h2
  rw [he, h] at h1
  exact h1.trans h2

/-- **The sharp window.**  For `a > 0` and `β ≠ 1/2`, a bounded all-height landing
`B z̃_{1,γ} = v_{β,γ}` on a nonempty open interval exists exactly when `a < min(β, 1-β)`. -/
theorem exists_rigged_landing_iff {a β : ℝ} (ha : 0 < a) (hβ : β ∈ Ioo 0 1) (hβ2 : β ≠ 1 / 2)
    {c d : ℝ} (hcd : c < d) :
    (∃ B : ℓ²ℕ →L[ℂ] ℓ²P, ∀ γ ∈ Ioo c d, B (riggedSource a 1 γ) = seamVector β hβ γ) ↔
      a < min β (1 - β) := by
  constructor
  · rintro ⟨B, hB⟩
    have hb : BddAbove (range fun p : Nat.Primes => seamLogProfile (2 * a + 1) β p) := by
      refine ⟨‖B‖, ?_⟩
      rintro _ ⟨p, rfl⟩
      have := norm_riggedMultiplier_le_of_rigged_landing ha hβ B hcd hB p
      rwa [norm_riggedMultiplier] at this
    have := (bddAbove_seamLogProfile_iff hβ2).mp hb
    linarith
  · intro hw
    exact ⟨riggedOp a 1 β (by simpa using hw), fun γ _ => riggedOp_one_riggedSource hβ ha hw γ⟩

end RHTower
