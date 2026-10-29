import GaloisForLFunctions.HeckeKreinToeplitz.FiniteIndexIsPositiveMinusFiniteRank
import GaloisForLFunctions.HeckeKreinToeplitz.OneGridHidesTwoGridsDecide

/-!
# The index under rotation, damping and coalescence

Which deformations of a kernel move its index, and how.

**Rotation** (`negIndex_twist`). Multiplying a kernel by a unitary character is a diagonal unitary
congruence of every Gram matrix, so the index is unchanged. On `ℚ_{>0}` this is the vertical shift
`ρ ↦ ρ + iτ` of all zeros at once. It is also the Liouville twist of a completely multiplicative
weight.

**Damping** (`negIndex_mul_sum_le`). Multiplying by a nonnegative combination of `r` unitary
characters, a positive-definite kernel of rank `r`, multiplies the index by at most `r`. The proof
is subadditivity plus rotation. The bound is attained (`negIndex_damped_pair_eq_two`): on `ℤ` the
positive-definite damping `1 + (−1)^n` turns one hyperbolic pair into two. Positive damping is not
index-nonincreasing.

**Coalescence** (`coalescence_law`). The pair `h_t` of logarithmic characters `u^{t+iγ}` has
exactly one negative square for every `t ≠ 0`. As `t → 0` it converges pointwise to
`2 Re ω · u^{iγ}`, the kernel of an on-line point of mass `2 Re ω` (`pairKernel_logChar_imag`).
For `Re ω ≥ 0` the limit has no negative square. So the index is only lower semicontinuous, and a
pair loses its square by coalescing onto the critical line. This is the coalescence blind spot of
the census in kernel form: at the limit, a coalesced off-line pair and a double on-line zero are
the same kernel. For `Re ω < 0` the square survives the limit (`negIndex_pairKernel_of_re_neg`).
-/

open Complex Finset Filter Matrix Topology
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.HeckeKreinToeplitz

variable {G : Type*} [Group G]

theorem inv_eq_conj_of_unitary {χ : G →* ℂ} (hχ : IsUnitaryChar χ) (u : G) :
    (χ u)⁻¹ = conj (χ u) := by
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hχ u]
  simp

theorem isPosDefKernel_zero : IsPosDefKernel (fun _ : G => (0 : ℂ)) :=
  ⟨fun _ => by simp, fun n x c => by rw [hermQuad_gram]; simp⟩

theorem negIndex_zero : negIndex (fun _ : G => (0 : ℂ)) = 0 :=
  negIndex_eq_zero_iff.mpr fun n x c => isPosDefKernel_zero.2 n x c

/-! ### Rotation -/

/-- A unitary twist is a diagonal congruence of the Toeplitz form. -/
theorem hermQuad_gram_twist {χ : G →* ℂ} (hχ : IsUnitaryChar χ) (k : G → ℂ) {ι : Type*}
    [Fintype ι] (x : ι → G) (c : ι → ℂ) :
    hermQuad (gram (fun u => χ u * k u) x) c = hermQuad (gram k x) fun b => χ (x b) * c b := by
  rw [hermQuad_gram, hermQuad_gram]
  congr 1
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  rw [map_mul, map_inv_eq_inv, inv_eq_conj_of_unitary hχ, map_mul]
  ring

theorem negIndex_twist_le {χ : G →* ℂ} (hχ : IsUnitaryChar χ) (k : G → ℂ) :
    negIndex (fun u => χ u * k u) ≤ negIndex k := by
  refine negIndex_le_iff.mpr fun n x => le_trans ?_ (hermNegIndex_gram_le_negIndex k x)
  refine Nat.cast_le.mpr (hermNegIndex_le_of_hermQuad_eq _ _
    (mulVecLin (diagonal fun b => χ (x b))) fun c => ?_)
  rw [mulVecLin_apply, hermQuad_gram_twist hχ]
  congr 1
  funext b
  rw [mulVec_diagonal]

/-- The conjugate of a character. -/
def conjChar (χ : G →* ℂ) : G →* ℂ := (starRingEnd ℂ).toMonoidHom.comp χ

theorem isUnitaryChar_conjChar {χ : G →* ℂ} (hχ : IsUnitaryChar χ) : IsUnitaryChar (conjChar χ) :=
  fun u => by simp [conjChar, hχ u]

theorem conjChar_mul_self {χ : G →* ℂ} (hχ : IsUnitaryChar χ) (u : G) : conjChar χ u * χ u = 1 := by
  show conj (χ u) * χ u = 1
  rw [← inv_eq_conj_of_unitary hχ, inv_mul_cancel₀ (map_ne_zero χ u)]

/-- **Rotation keeps the index.** -/
theorem negIndex_twist {χ : G →* ℂ} (hχ : IsUnitaryChar χ) (k : G → ℂ) :
    negIndex (fun u => χ u * k u) = negIndex k := by
  refine le_antisymm (negIndex_twist_le hχ k) ?_
  calc negIndex k = negIndex (fun u => conjChar χ u * (χ u * k u)) := by
        congr 1
        funext u
        rw [← mul_assoc, conjChar_mul_self hχ, one_mul]
    _ ≤ negIndex (fun u => χ u * k u) := negIndex_twist_le (isUnitaryChar_conjChar hχ) _

/-! ### Damping -/

/-- A nonnegative scaling does not raise the index. -/
theorem negIndex_smul_le {a : ℝ} (ha : 0 ≤ a) (k : G → ℂ) :
    negIndex (fun u => (a : ℂ) * k u) ≤ negIndex k := by
  refine negIndex_le_iff.mpr fun n x => le_trans ?_ (hermNegIndex_gram_le_negIndex k x)
  refine Nat.cast_le.mpr (hermNegIndex_le_of_hermQuad_eq _ _
    ((Real.sqrt a : ℂ) • LinearMap.id) fun c => ?_)
  rw [hermQuad_gram, hermQuad_gram]
  simp only [LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply, smul_eq_mul, map_mul,
    conj_ofReal]
  have hs : ((Real.sqrt a : ℝ) : ℂ) * (Real.sqrt a : ℂ) = a := by
    rw [← ofReal_mul, Real.mul_self_sqrt ha]
  congr 1
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  linear_combination (conj (c i) * k ((x i)⁻¹ * x j) * c j) * hs

theorem isHermKernel_mul_sum {J : Type*} (s : Finset J) {χ : J → G →* ℂ}
    (hχ : ∀ j, IsUnitaryChar (χ j)) (a : J → ℝ) {k : G → ℂ} (hk : IsHermKernel k) :
    IsHermKernel (fun u => (∑ j ∈ s, (a j : ℂ) * χ j u) * k u) := fun u => by
  show (∑ j ∈ s, (a j : ℂ) * χ j u⁻¹) * k u⁻¹ = conj ((∑ j ∈ s, (a j : ℂ) * χ j u) * k u)
  rw [hk, map_mul, map_sum]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  rw [map_mul, conj_ofReal, map_inv_eq_inv, inv_eq_conj_of_unitary (hχ j)]

/-- **Damping by `r` unitary characters multiplies the index by at most `r`.** -/
theorem negIndex_mul_sum_le {J : Type*} [DecidableEq J] (s : Finset J) {χ : J → G →* ℂ}
    (hχ : ∀ j, IsUnitaryChar (χ j)) {a : J → ℝ} (ha : ∀ j, 0 ≤ a j) {k : G → ℂ}
    (hk : IsHermKernel k) :
    negIndex (fun u => (∑ j ∈ s, (a j : ℂ) * χ j u) * k u) ≤ s.card * negIndex k := by
  induction s using Finset.induction_on with
  | empty => simpa using negIndex_zero.le
  | insert j s hj ih =>
    have hsplit : (fun u => (∑ i ∈ insert j s, (a i : ℂ) * χ i u) * k u) =
        fun u => (a j : ℂ) * χ j u * k u + (∑ i ∈ s, (a i : ℂ) * χ i u) * k u :=
      funext fun u => by rw [sum_insert hj]; ring
    have hH1 : IsHermKernel (fun u => (a j : ℂ) * χ j u * k u) := by
      simpa using isHermKernel_mul_sum {j} hχ a hk
    have h1 : negIndex (fun u => (a j : ℂ) * χ j u * k u) ≤ negIndex k :=
      calc negIndex (fun u => (a j : ℂ) * χ j u * k u)
          = negIndex (fun u => (a j : ℂ) * (χ j u * k u)) := by simp only [mul_assoc]
        _ ≤ negIndex (fun u => χ j u * k u) := negIndex_smul_le (ha j) _
        _ = negIndex k := negIndex_twist (hχ j) k
    rw [hsplit, card_insert_of_notMem hj]
    refine (negIndex_add_le hH1 (isHermKernel_mul_sum s hχ a hk)).trans ?_
    calc _ ≤ negIndex k + s.card * negIndex k := add_le_add h1 ih
      _ = ((s.card + 1 : ℕ) : ℕ∞) * negIndex k := by push_cast; ring

/-- **Damping can double the index.** On `ℤ`, `(1 + (−1)^n)(2^n + 2^{−n})` is the sum of the pairs
at `2` and at `−2`. -/
theorem negIndex_damped_pair_eq_two :
    negIndex (fun n : Multiplicative ℤ =>
      (valChar 1 n + valChar (-1) n) * pairKernel (valChar 2) 1 n) = 2 := by
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  have hm2 : (-2 : ℂ) ≠ 0 := by norm_num
  set χ : Fin 2 → Multiplicative ℤ →* ℂ := ![valChar 2, valChar (-2)]
  have hk : (fun n : Multiplicative ℤ =>
      (valChar 1 n + valChar (-1) n) * pairKernel (valChar 2) 1 n) =
      fun n => (fun _ => (0 : ℂ)) n + ∑ j, pairKernel (χ j) ((fun _ => (1 : ℂ)) j) n := by
    funext n
    have hv : ∀ v : ℂ, v ≠ 0 → valChar v n = v ^ Multiplicative.toAdd n := fun v hv => by
      simp [valChar, hv]
    have hr : ∀ v : ℂ, v ≠ 0 → reflectChar (valChar v) n = (conj v)⁻¹ ^ Multiplicative.toAdd n :=
      fun v hv' => by rw [reflectChar_apply, map_inv_eq_inv, hv v hv', map_inv₀, map_zpow₀, _root_.inv_zpow]
    simp only [Fin.sum_univ_two, χ, Matrix.cons_val_zero, Matrix.cons_val_one, pairKernel, map_one,
      one_mul, zero_add]
    rw [hv 1 one_ne_zero, hv (-1) (by norm_num), hv 2 h2, hv (-2) hm2, hr 2 h2, hr (-2) hm2]
    set m := Multiplicative.toAdd n
    have e1 : (-2 : ℂ) ^ m = (-1) ^ m * 2 ^ m := by rw [← mul_zpow]; norm_num
    have e2 : (-(2 : ℂ)⁻¹) ^ m = (-1) ^ m * 2⁻¹ ^ m := by rw [← mul_zpow]; norm_num
    simp only [Complex.conj_ofNat, map_neg, inv_neg, _root_.one_zpow]
    rw [e1, e2]
    ring
  rw [hk, negIndex_add_sum_pairKernel_eq isPosDefKernel_zero χ _ (fun _ => one_ne_zero)
    (Multiplicative.ofAdd 1)]
  · rfl
  · intro j
    fin_cases j <;> simp [χ, valChar_ofAdd_one h2, valChar_ofAdd_one hm2]
  · have hnodes : nodes χ (Multiplicative.ofAdd 1) = Sum.elim ![2, -2] ![2⁻¹, -2⁻¹] := by
      funext a
      rcases a with a | a <;> fin_cases a
      · exact valChar_ofAdd_one h2
      · exact valChar_ofAdd_one hm2
      · show reflectChar (valChar 2) _ = _
        rw [reflectChar_valChar_ofAdd_one h2, Complex.conj_ofNat]
        rfl
      · show reflectChar (valChar (-2)) _ = _
        rw [reflectChar_valChar_ofAdd_one hm2, map_neg, Complex.conj_ofNat, inv_neg]
        rfl
    rw [hnodes]
    intro a b hab
    rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b
    all_goals first | rfl | (norm_num at hab)

/-! ### Coalescence -/

section Coalescence

variable (ℓ : G →* Multiplicative ℝ)

theorem isUnitaryChar_logChar_imag (γ : ℝ) : IsUnitaryChar (logChar ℓ (γ * I)) := fun u => by
  rw [norm_logChar]
  simp

/-- **A coalesced pair is an on-line point of mass `2 Re ω`.** -/
theorem pairKernel_logChar_imag (γ : ℝ) (ω : ℂ) :
    pairKernel (logChar ℓ (γ * I)) ω = fun u => ((2 * ω.re : ℝ) : ℂ) * logChar ℓ (γ * I) u := by
  funext u
  rw [pairKernel, reflectChar_eq_of_unitary (isUnitaryChar_logChar_imag ℓ γ), ← add_mul,
    Complex.add_conj]

/-- A pair approaching the line converges pointwise to its coalesced kernel. -/
theorem tendsto_pairKernel_logChar (γ : ℝ) (ω : ℂ) :
    Tendsto (fun t : ℝ => pairKernel (logChar ℓ ((t : ℂ) + γ * I)) ω) (𝓝 0)
      (𝓝 (pairKernel (logChar ℓ (γ * I)) ω)) := by
  rw [tendsto_pi_nhds]
  intro u
  have hcont : Continuous fun t : ℝ => pairKernel (logChar ℓ ((t : ℂ) + γ * I)) ω u := by
    simp only [pairKernel, reflectChar_logChar, logChar_apply]
    fun_prop
  simpa using hcont.tendsto 0

/-- Off the line the pair carries exactly one negative square. -/
theorem negIndex_pairKernel_logChar_eq_one {u₀ : G} (hu₀ : scale ℓ u₀ ≠ 0) {t : ℝ} (ht : t ≠ 0)
    (γ : ℝ) {ω : ℂ} (hω : ω ≠ 0) :
    negIndex (pairKernel (logChar ℓ ((t : ℂ) + γ * I)) ω) = 1 := by
  have hχ : ¬ IsUnitaryChar (logChar ℓ ((t : ℂ) + γ * I)) := fun h => by
    have h1 := h u₀
    rw [norm_logChar, Real.exp_eq_one_iff] at h1
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero,
      add_zero] at h1
    exact (mul_ne_zero ht hu₀) h1
  simpa using negIndex_add_pairKernel_eq_one isPosDefKernel_zero hχ hω

/-- A unitary pair with `Re ω < 0` keeps one negative square. -/
theorem negIndex_pairKernel_of_re_neg {χ : G →* ℂ} (hχ : IsUnitaryChar χ) {ω : ℂ}
    (hω : ω.re < 0) : negIndex (pairKernel χ ω) = 1 := by
  refine le_antisymm ?_ ?_
  · simpa using negIndex_add_sum_pairKernel_le isPosDefKernel_zero (fun _ : Fin 1 => χ)
      (fun _ => ω)
  · by_contra h
    have h0 : negIndex (pairKernel χ ω) = 0 := Order.lt_one_iff.mp (not_le.mp h)
    have := negIndex_eq_zero_iff.mp h0 1 (fun _ => 1) (fun _ => 1)
    rw [hermQuad_gram_pairKernel_of_unitary hχ] at this
    have hpos : 0 < normSq (charEval χ (fun _ : Fin 1 => (1 : G)) fun _ => 1) := by
      rw [normSq_pos, charEval_apply]
      simp
    nlinarith

/-- **The coalescence law.** Off the line a pair has one negative square for every `t ≠ 0`; it
converges pointwise to the on-line point `2 Re ω · u^{iγ}`, which has none when `Re ω ≥ 0`. -/
theorem coalescence_law {u₀ : G} (hu₀ : scale ℓ u₀ ≠ 0) (γ : ℝ) {ω : ℂ} (hω : ω ≠ 0)
    (hre : 0 ≤ ω.re) :
    (∀ t : ℝ, t ≠ 0 → negIndex (pairKernel (logChar ℓ ((t : ℂ) + γ * I)) ω) = 1) ∧
      Tendsto (fun t : ℝ => pairKernel (logChar ℓ ((t : ℂ) + γ * I)) ω) (𝓝 0)
        (𝓝 fun u => ((2 * ω.re : ℝ) : ℂ) * logChar ℓ (γ * I) u) ∧
      negIndex (fun u => ((2 * ω.re : ℝ) : ℂ) * logChar ℓ (γ * I) u) = 0 := by
  refine ⟨fun t ht => negIndex_pairKernel_logChar_eq_one ℓ hu₀ ht γ hω, ?_, ?_⟩
  · rw [← pairKernel_logChar_imag]
    exact tendsto_pairKernel_logChar ℓ γ ω
  · rw [← pairKernel_logChar_imag]
    exact negIndex_pairKernel_of_unitary (isUnitaryChar_logChar_imag ℓ γ) hre

end Coalescence

end GaloisForLFunctions.HeckeKreinToeplitz
