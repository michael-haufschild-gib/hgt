import GaloisForLFunctions.RHTower.HyperKloostermanSecondMomentKernel
import GaloisForLFunctions.HTGeometry.UnitPowerSumOscillation

/-!
# Completing interval sums of products of periodic functions

For `A : ZMod n → ℂ` put `Â(h) = Σ_y A(y) e(-hy/n)`, so that `A(x) = n⁻¹ Σ_h Â(h) e(hx/n)`
(`fourier_inversion`). Let `n₁, n₂, n₃` be pairwise coprime, `M = n₁n₂n₃`, and
`f(m) = A₁(m) A₂(m) B(m)`. Then `Σ_{1≤m≤L} f(m) = M⁻¹ Σ_h Â₁(h₁)Â₂(h₂)B̂(h₃) Σ_m z(h)^m` with
`z(h) = e(h₁/n₁ + h₂/n₂ + h₃/n₃)`.

* By the Chinese remainder theorem, `z(h) = e(K(h)/M)` with `K(h)` injective modulo `M`
  (`kFreq_mod_injective`).
* For `0 < j < M`, `|e(j/M) - 1| ≥ 4 min(j, M-j)/M` by Jordan's inequality
  (`norm_exp_sub_one_ge`). Hence `Σ_{0<j<M} 2/|e(j/M) - 1| ≤ M(1 + log M)`
  (`sum_two_div_norm_exp_sub_one_le`).
* Every geometric sum `Σ_{1≤m≤L} z^m` with `z ≠ 1` on the unit circle is at most `2/|z - 1|`.

Suppose `d ∣ n₃`, `|Â₁| ≤ α₁`, `|Â₂| ≤ α₂`, `|B̂(h₃)| ≤ β_gen` for `d ∤ h₃`, and `|B̂| ≤ β_all`. The
frequencies with `d ∣ h₃` are `(M/d)`-th roots of unity, and this gives
`|Σ_{1≤m≤L} f(m)| ≤ (L/M)|Â₁(0)Â₂(0)B̂(0)| + α₁α₂β_gen(1 + log M) + α₁α₂β_all/d · (1 + log(M/d))`
(`norm_sum_Icc_triple_le`).
-/

open Finset

namespace GaloisForLFunctions.RHTower.RootOfUnityCompletion

open GaloisForLFunctions.RHTower.HyperKloostermanSecondMoment

noncomputable section

/-- **Distance of a root of unity from `1`.** For `0 < K < M`,
`‖e(K/M) - 1‖ ≥ 4 min(K, M - K)/M`, by `|e(θ) - 1| = 2|sin πθ|` and Jordan's inequality. -/
theorem norm_exp_sub_one_ge {M K : ℕ} (hK0 : 0 < K) (hKM : K < M) :
    4 * ((min K (M - K) : ℕ) : ℝ) / M ≤
      ‖Complex.exp (2 * Real.pi * Complex.I * K / M) - 1‖ := by
  have hM : (0 : ℝ) < M := by exact_mod_cast (hK0.trans hKM)
  have harg : 2 * (Real.pi : ℂ) * Complex.I * K / M = Complex.I * ((2 * Real.pi * K / M : ℝ) : ℂ) := by
    push_cast; ring
  rw [harg, Complex.norm_exp_I_mul_ofReal_sub_one]
  have hhalf : 2 * Real.pi * K / M / 2 = Real.pi * (K / M) := by ring
  rw [hhalf, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_two]
  set θ : ℝ := K / M with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one hM]; exact_mod_cast hKM.le
  rcases le_total K (M - K) with hle | hle
  · have hmin : ((min K (M - K) : ℕ) : ℝ) = K := by rw [min_eq_left hle]
    have hθh : θ ≤ 1 / 2 := by
      rw [hθ, div_le_iff₀ hM]
      have : (K : ℝ) ≤ (M - K : ℕ) := by exact_mod_cast hle
      rw [Nat.cast_sub hKM.le] at this
      linarith
    have hs := Real.mul_le_sin (x := Real.pi * θ) (by positivity) (by nlinarith [Real.pi_pos])
    have hs' : 2 * θ ≤ Real.sin (Real.pi * θ) := by
      have : 2 / Real.pi * (Real.pi * θ) = 2 * θ := by field_simp
      linarith
    rw [hmin, abs_of_nonneg (by linarith)]
    have : 4 * (K : ℝ) / M = 2 * (2 * θ) := by rw [hθ]; ring
    rw [this]
    linarith
  · have hmin : ((min K (M - K) : ℕ) : ℝ) = (M - K : ℕ) := by rw [min_eq_right hle]
    have hMK : ((M - K : ℕ) : ℝ) = M - K := by rw [Nat.cast_sub hKM.le]
    have hθh : 1 / 2 ≤ θ := by
      rw [hθ, le_div_iff₀ hM]
      have : ((M - K : ℕ) : ℝ) ≤ K := by exact_mod_cast hle
      rw [hMK] at this
      linarith
    have hs := Real.mul_le_sin (x := Real.pi * (1 - θ)) (by nlinarith [Real.pi_pos])
      (by nlinarith [Real.pi_pos])
    have hs' : 2 * (1 - θ) ≤ Real.sin (Real.pi * θ) := by
      have e1 : Real.sin (Real.pi * (1 - θ)) = Real.sin (Real.pi * θ) := by
        rw [show Real.pi * (1 - θ) = Real.pi - Real.pi * θ by ring, Real.sin_pi_sub]
      have : 2 / Real.pi * (Real.pi * (1 - θ)) = 2 * (1 - θ) := by field_simp
      linarith
    rw [hmin, hMK, abs_of_nonneg (by linarith)]
    have : 4 * ((M : ℝ) - K) / M = 2 * (2 * (1 - θ)) := by rw [hθ]; field_simp; ring
    rw [this]
    linarith

/-- Termwise harmonic majorant: `2/‖e(K/M) - 1‖ ≤ (M/2)(1/K + 1/(M - K))` for `0 < K < M`. -/
theorem two_div_norm_exp_sub_one_le {M K : ℕ} (hK0 : 0 < K) (hKM : K < M) :
    2 / ‖Complex.exp (2 * Real.pi * Complex.I * K / M) - 1‖ ≤
      (M / 2 : ℝ) * (1 / K + 1 / ((M - K : ℕ) : ℝ)) := by
  have hM : (0 : ℝ) < M := by exact_mod_cast (hK0.trans hKM)
  have hK : (0 : ℝ) < K := by exact_mod_cast hK0
  have hMK : (0 : ℝ) < ((M - K : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hKM
  have hmin0 : (0 : ℝ) < ((min K (M - K) : ℕ) : ℝ) := by
    exact_mod_cast lt_min hK0 (Nat.sub_pos_of_lt hKM)
  have hge := norm_exp_sub_one_ge hK0 hKM
  have hpos : 0 < 4 * ((min K (M - K) : ℕ) : ℝ) / M := by positivity
  calc 2 / ‖Complex.exp (2 * Real.pi * Complex.I * K / M) - 1‖
      ≤ 2 / (4 * ((min K (M - K) : ℕ) : ℝ) / M) := div_le_div_of_nonneg_left (by norm_num) hpos hge
    _ = (M / 2 : ℝ) * (1 / ((min K (M - K) : ℕ) : ℝ)) := by field_simp; ring
    _ ≤ (M / 2 : ℝ) * (1 / K + 1 / ((M - K : ℕ) : ℝ)) := by
        gcongr
        rcases le_total K (M - K) with hle | hle
        · rw [min_eq_left hle]
          have : (0 : ℝ) ≤ 1 / ((M - K : ℕ) : ℝ) := by positivity
          linarith
        · rw [min_eq_right hle]
          have : (0 : ℝ) ≤ 1 / (K : ℝ) := by positivity
          linarith

/-- **Harmonic bound over the nontrivial `N`-th roots of unity:**
`Σ_{0<j<N} 2/‖e(j/N) - 1‖ ≤ N (1 + log N)`. -/
theorem sum_two_div_norm_exp_sub_one_le (N : ℕ) :
    ∑ j ∈ Finset.Ioo 0 N, 2 / ‖Complex.exp (2 * Real.pi * Complex.I * j / N) - 1‖ ≤
      N * (1 + Real.log N) := by
  have hrefl : ∑ j ∈ Finset.Ioo 0 N, (1 : ℝ) / ((N - j : ℕ) : ℝ) =
      ∑ j ∈ Finset.Ioo 0 N, (1 : ℝ) / j := by
    refine Finset.sum_nbij' (fun j => N - j) (fun j => N - j) ?_ ?_ ?_ ?_ ?_
    · intro j hj; simp only [Finset.mem_Ioo] at hj ⊢; omega
    · intro j hj; simp only [Finset.mem_Ioo] at hj ⊢; omega
    · intro j hj; simp only [Finset.mem_Ioo] at hj; omega
    · intro j hj; simp only [Finset.mem_Ioo] at hj; omega
    · intro j hj; rfl
  have hH : ∑ j ∈ Finset.Ioo 0 N, (1 : ℝ) / j ≤ 1 + Real.log N := by
    refine le_trans ?_ (harmonic_le_one_add_log N)
    rw [harmonic_eq_sum_Icc]
    push_cast
    simp only [one_div]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => by positivity)
    intro j hj
    simp only [Finset.mem_Ioo] at hj
    simp only [Finset.mem_Icc]
    omega
  calc ∑ j ∈ Finset.Ioo 0 N, 2 / ‖Complex.exp (2 * Real.pi * Complex.I * j / N) - 1‖
      ≤ ∑ j ∈ Finset.Ioo 0 N, (N / 2 : ℝ) * (1 / j + 1 / ((N - j : ℕ) : ℝ)) := by
        refine Finset.sum_le_sum fun j hj => ?_
        simp only [Finset.mem_Ioo] at hj
        exact two_div_norm_exp_sub_one_le hj.1 hj.2
    _ = (N / 2 : ℝ) * (∑ j ∈ Finset.Ioo 0 N, (1 : ℝ) / j +
          ∑ j ∈ Finset.Ioo 0 N, (1 : ℝ) / ((N - j : ℕ) : ℝ)) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
    _ = N * ∑ j ∈ Finset.Ioo 0 N, (1 : ℝ) / j := by rw [hrefl]; ring
    _ ≤ N * (1 + Real.log N) := by gcongr

/-- The discrete Fourier coefficient `Â(h) = Σ_y A(y) e(-hy/n)`. -/
def fourierCoeff {n : ℕ} [NeZero n] (A : ZMod n → ℂ) (h : ZMod n) : ℂ :=
  ∑ y : ZMod n, A y * ZMod.stdAddChar (-(h * y))

/-- **Fourier inversion on `ZMod n`:** `A(x) = n⁻¹ Σ_h Â(h) e(hx/n)`. -/
theorem fourier_inversion {n : ℕ} [NeZero n] (A : ZMod n → ℂ) (x : ZMod n) :
    A x = (n : ℂ)⁻¹ * ∑ h : ZMod n, fourierCoeff A h * ZMod.stdAddChar (h * x) := by
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have key : ∑ h : ZMod n, fourierCoeff A h * ZMod.stdAddChar (h * x) =
      ∑ y : ZMod n, A y * ∑ h : ZMod n, ZMod.stdAddChar (h * (x - y)) := by
    simp only [fourierCoeff, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun h _ => ?_
    rw [mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  rw [key]
  simp_rw [sum_stdAddChar_mul, sub_eq_zero]
  rw [Finset.sum_eq_single x]
  · rw [if_pos rfl]; field_simp
  · intro y _ hy; rw [if_neg (Ne.symm hy), mul_zero]
  · intro h; exact absurd (Finset.mem_univ x) h

/-- Geometric sums over `[1, L]` of a point on the closed unit disc other than `1`. -/
theorem norm_sum_Icc_pow_le {z : ℂ} (hz : ‖z‖ ≤ 1) (hz1 : z ≠ 1) (L : ℕ) :
    ‖∑ m ∈ Finset.Icc 1 L, z ^ m‖ ≤ 2 / ‖z - 1‖ := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  simp_rw [add_comm 1]
  exact GaloisForLFunctions.HTGeometry.norm_sum_pow_succ_le hz hz1 L

/-- A root of unity `e(j/M)` with `0 < j < M` has norm one and is not `1`. -/
theorem exp_root_ne_one {M j : ℕ} (hj0 : 0 < j) (hjM : j < M) :
    Complex.exp (2 * Real.pi * Complex.I * j / M) ≠ 1 := by
  intro h
  have hge := norm_exp_sub_one_ge hj0 hjM
  rw [h, sub_self, norm_zero] at hge
  have hM : (0 : ℝ) < M := by exact_mod_cast (hj0.trans hjM)
  have hmin : (0 : ℝ) < ((min j (M - j) : ℕ) : ℝ) := by
    exact_mod_cast lt_min hj0 (Nat.sub_pos_of_lt hjM)
  have : 0 < 4 * ((min j (M - j) : ℕ) : ℝ) / M := by positivity
  linarith

theorem norm_exp_root (M j : ℕ) : ‖Complex.exp (2 * Real.pi * Complex.I * j / M)‖ = 1 := by
  rw [Complex.norm_exp]
  have : (2 * Real.pi * Complex.I * j / M).re = 0 := by
    simp [Complex.div_re, Complex.mul_re, Complex.mul_im]
  rw [this, Real.exp_zero]

/-- The combined frequency of three characters with coprime moduli. -/
def kFreq (n₁ n₂ n₃ : ℕ) (h : ZMod n₁ × ZMod n₂ × ZMod n₃) : ℕ :=
  h.1.val * (n₂ * n₃) + h.2.1.val * (n₁ * n₃) + h.2.2.val * (n₁ * n₂)

variable {n₁ n₂ n₃ : ℕ} [NeZero n₁] [NeZero n₂] [NeZero n₃]

/-- `e(h₁/n₁) e(h₂/n₂) e(h₃/n₃) = e(K/(n₁n₂n₃))` with `K = kFreq h`. -/
theorem stdAddChar_triple (h : ZMod n₁ × ZMod n₂ × ZMod n₃) :
    ZMod.stdAddChar h.1 * ZMod.stdAddChar h.2.1 * ZMod.stdAddChar h.2.2 =
      Complex.exp (2 * Real.pi * Complex.I * (kFreq n₁ n₂ n₃ h : ℕ) / ((n₁ * n₂ * n₃ : ℕ) : ℂ)) := by
  simp only [ZMod.stdAddChar_apply, ZMod.toCircle_apply, ← Complex.exp_add]
  congr 1
  have h1 : (n₁ : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n₁
  have h2 : (n₂ : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n₂
  have h3 : (n₃ : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n₃
  simp only [kFreq]
  push_cast
  field_simp

/-- Reduction of the frequency modulo `M`. -/
theorem exp_kFreq_mod (K M : ℕ) (hM : 0 < M) :
    Complex.exp (2 * Real.pi * Complex.I * (K : ℕ) / (M : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (K % M : ℕ) / (M : ℂ)) := by
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  conv_lhs => rw [← Nat.div_add_mod K M]
  push_cast
  have : 2 * (Real.pi : ℂ) * Complex.I * ((M : ℂ) * ((K / M : ℕ) : ℂ) + ((K % M : ℕ) : ℂ)) / M =
      ((K / M : ℕ) : ℂ) * (2 * Real.pi * Complex.I) + 2 * Real.pi * Complex.I * ((K % M : ℕ) : ℂ) / M := by
    field_simp
  rw [this, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, one_mul]

omit [NeZero n₂] [NeZero n₃] in
theorem kFreq_cast_fst (h : ZMod n₁ × ZMod n₂ × ZMod n₃) :
    ((kFreq n₁ n₂ n₃ h : ℕ) : ZMod n₁) = h.1 * ((n₂ * n₃ : ℕ) : ZMod n₁) := by
  simp only [kFreq]
  push_cast
  rw [ZMod.natCast_self, ZMod.natCast_zmod_val]
  ring

omit [NeZero n₁] [NeZero n₃] in
theorem kFreq_cast_snd (h : ZMod n₁ × ZMod n₂ × ZMod n₃) :
    ((kFreq n₁ n₂ n₃ h : ℕ) : ZMod n₂) = h.2.1 * ((n₁ * n₃ : ℕ) : ZMod n₂) := by
  simp only [kFreq]
  push_cast
  rw [ZMod.natCast_self, ZMod.natCast_zmod_val]
  ring

omit [NeZero n₁] [NeZero n₂] in
theorem kFreq_cast_thd (h : ZMod n₁ × ZMod n₂ × ZMod n₃) :
    ((kFreq n₁ n₂ n₃ h : ℕ) : ZMod n₃) = h.2.2 * ((n₁ * n₂ : ℕ) : ZMod n₃) := by
  simp only [kFreq]
  push_cast
  rw [ZMod.natCast_self, ZMod.natCast_zmod_val]
  ring

/-- **The combined frequency is injective modulo `n₁n₂n₃`** (Chinese remainder theorem). -/
theorem kFreq_mod_injective (h12 : n₁.Coprime n₂) (h13 : n₁.Coprime n₃) (h23 : n₂.Coprime n₃)
    {h h' : ZMod n₁ × ZMod n₂ × ZMod n₃}
    (he : kFreq n₁ n₂ n₃ h % (n₁ * n₂ * n₃) = kFreq n₁ n₂ n₃ h' % (n₁ * n₂ * n₃)) : h = h' := by
  have hmod : kFreq n₁ n₂ n₃ h ≡ kFreq n₁ n₂ n₃ h' [MOD n₁ * n₂ * n₃] := he
  have m1 : kFreq n₁ n₂ n₃ h ≡ kFreq n₁ n₂ n₃ h' [MOD n₁] :=
    Nat.ModEq.of_mul_right (n₂ * n₃) (by rwa [← mul_assoc])
  have m2 : kFreq n₁ n₂ n₃ h ≡ kFreq n₁ n₂ n₃ h' [MOD n₂] :=
    Nat.ModEq.of_mul_right (n₁ * n₃) (by rwa [show n₂ * (n₁ * n₃) = n₁ * n₂ * n₃ by ring])
  have m3 : kFreq n₁ n₂ n₃ h ≡ kFreq n₁ n₂ n₃ h' [MOD n₃] :=
    Nat.ModEq.of_mul_left (n₁ * n₂) hmod
  have c1 := (ZMod.natCast_eq_natCast_iff _ _ _).2 m1
  have c2 := (ZMod.natCast_eq_natCast_iff _ _ _).2 m2
  have c3 := (ZMod.natCast_eq_natCast_iff _ _ _).2 m3
  rw [kFreq_cast_fst, kFreq_cast_fst] at c1
  rw [kFreq_cast_snd, kFreq_cast_snd] at c2
  rw [kFreq_cast_thd, kFreq_cast_thd] at c3
  have u1 := ZMod.coe_unitOfCoprime (n₂ * n₃) (Nat.Coprime.mul_right h12 h13).symm
  have u2 := ZMod.coe_unitOfCoprime (n₁ * n₃) (Nat.Coprime.mul_right h12.symm h23).symm
  have u3 := ZMod.coe_unitOfCoprime (n₁ * n₂) (Nat.Coprime.mul_right h13.symm h23.symm).symm
  rw [← u1, Units.mul_left_inj] at c1
  rw [← u2, Units.mul_left_inj] at c2
  rw [← u3, Units.mul_left_inj] at c3
  obtain ⟨a, b, c⟩ := h
  obtain ⟨a', b', c'⟩ := h'
  simp only at c1 c2 c3
  rw [c1, c2, c3]

theorem stdAddChar_mul_natCast_pow {n : ℕ} [NeZero n] (h : ZMod n) (m : ℕ) :
    ZMod.stdAddChar (h * (m : ZMod n)) = ZMod.stdAddChar h ^ m := by
  rw [mul_comm, ← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]

/-- Reversal of three finite sums. -/
theorem sum_comm_three_rev {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℂ) : ∑ a, ∑ b, ∑ c, f a b c = ∑ c, ∑ b, ∑ a, f a b c := by
  calc ∑ a, ∑ b, ∑ c, f a b c = ∑ a, ∑ c, ∑ b, f a b c :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, f a b c := Finset.sum_comm
    _ = ∑ c, ∑ b, ∑ a, f a b c := Finset.sum_congr rfl fun c _ => Finset.sum_comm

/-- The product of three characters, as a function of the frequency triple. -/
def zTriple (h : ZMod n₁ × ZMod n₂ × ZMod n₃) : ℂ :=
  ZMod.stdAddChar h.1 * ZMod.stdAddChar h.2.1 * ZMod.stdAddChar h.2.2

/-- Fourier expansion of a product of three periodic factors with coprime periods. -/
theorem triple_expansion (A₁ : ZMod n₁ → ℂ) (A₂ : ZMod n₂ → ℂ) (B : ZMod n₃ → ℂ) (m : ℕ) :
    A₁ (m : ZMod n₁) * A₂ (m : ZMod n₂) * B (m : ZMod n₃) =
      ((n₁ * n₂ * n₃ : ℕ) : ℂ)⁻¹ * ∑ h : ZMod n₁ × ZMod n₂ × ZMod n₃,
        fourierCoeff A₁ h.1 * fourierCoeff A₂ h.2.1 * fourierCoeff B h.2.2 * zTriple h ^ m := by
  rw [fourier_inversion A₁, fourier_inversion A₂, fourier_inversion B]
  simp_rw [stdAddChar_mul_natCast_pow]
  simp only [Fintype.sum_prod_type, zTriple, Finset.mul_sum, Finset.sum_mul]
  rw [sum_comm_three_rev]
  refine Finset.sum_congr rfl fun h₁ _ => Finset.sum_congr rfl fun h₂ _ =>
    Finset.sum_congr rfl fun h₃ _ => ?_
  push_cast
  rw [mul_pow, mul_pow, mul_inv, mul_inv]
  ring

/-- **Completion of an interval sum of three periodic factors.** Write
`M = n₁n₂n₃` with `n₁, n₂, n₃` pairwise coprime and `d ∣ n₃`. Bound the Fourier coefficients of the
factors by `α₁`, `α₂`, by `β_gen` at frequencies `h₃` with `d ∤ h₃` and by `β_all` everywhere.
The interval sum over `[1, L]` is then at most
`(L/M) c₀ + α₁α₂β_gen (1 + log M) + α₁α₂β_all/d · (1 + log (M/d))`. -/
theorem norm_sum_Icc_triple_le (h12 : n₁.Coprime n₂) (h13 : n₁.Coprime n₃) (h23 : n₂.Coprime n₃)
    {d N₃ : ℕ} (hd0 : 0 < d) (hdN : n₃ = d * N₃)
    (A₁ : ZMod n₁ → ℂ) (A₂ : ZMod n₂ → ℂ) (B : ZMod n₃ → ℂ) {α₁ α₂ βg βa c₀ : ℝ}
    (hA₁ : ∀ h, ‖fourierCoeff A₁ h‖ ≤ α₁) (hA₂ : ∀ h, ‖fourierCoeff A₂ h‖ ≤ α₂)
    (hβg : 0 ≤ βg) (hBg : ∀ h : ZMod n₃, ¬ d ∣ h.val → ‖fourierCoeff B h‖ ≤ βg)
    (hBa : ∀ h, ‖fourierCoeff B h‖ ≤ βa)
    (h0 : ‖fourierCoeff A₁ 0 * fourierCoeff A₂ 0 * fourierCoeff B 0‖ ≤ c₀) (L : ℕ) :
    ‖∑ m ∈ Finset.Icc 1 L, A₁ (m : ZMod n₁) * A₂ (m : ZMod n₂) * B (m : ZMod n₃)‖ ≤
      (L : ℝ) / (n₁ * n₂ * n₃ : ℕ) * c₀ +
        α₁ * α₂ * βg * (1 + Real.log (n₁ * n₂ * n₃ : ℕ)) +
        α₁ * α₂ * βa / d * (1 + Real.log (n₁ * n₂ * N₃ : ℕ)) := by
  classical
  set M := n₁ * n₂ * n₃ with hMdef
  set M' := n₁ * n₂ * N₃ with hM'def
  have hMM' : M = d * M' := by rw [hMdef, hM'def, hdN]; ring
  have hMpos : 0 < M := by
    have := NeZero.pos n₁; have := NeZero.pos n₂; have := NeZero.pos n₃; positivity
  have hM'pos : 0 < M' := by
    rcases Nat.eq_zero_or_pos M' with h | h
    · rw [hMM', h, mul_zero] at hMpos; exact absurd hMpos (lt_irrefl 0)
    · exact h
  have hMR : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hα₁ : 0 ≤ α₁ := (norm_nonneg _).trans (hA₁ 0)
  have hα₂ : 0 ≤ α₂ := (norm_nonneg _).trans (hA₂ 0)
  have hβa : 0 ≤ βa := (norm_nonneg _).trans (hBa 0)
  set C : ZMod n₁ × ZMod n₂ × ZMod n₃ → ℂ := fun h =>
    fourierCoeff A₁ h.1 * fourierCoeff A₂ h.2.1 * fourierCoeff B h.2.2 with hC
  set φ : ℕ → ℕ → ℝ := fun N j =>
    2 / ‖Complex.exp (2 * Real.pi * Complex.I * j / N) - 1‖ with hφ
  -- the combined frequency of a nonzero triple
  set jf : ZMod n₁ × ZMod n₂ × ZMod n₃ → ℕ := fun h => kFreq n₁ n₂ n₃ h % M with hjf
  have hjf_inj : ∀ h h', jf h = jf h' → h = h' := fun h h' he =>
    kFreq_mod_injective h12 h13 h23 he
  have hjf0 : jf 0 = 0 := by simp [hjf, kFreq]
  have hjf_pos : ∀ h, h ≠ 0 → 0 < jf h := by
    intro h hh
    rcases Nat.eq_zero_or_pos (jf h) with h' | h'
    · exact absurd (hjf_inj h 0 (h'.trans hjf0.symm)) hh
    · exact h'
  have hjf_lt : ∀ h, jf h < M := fun h => Nat.mod_lt _ hMpos
  have hz : ∀ h, zTriple h = Complex.exp (2 * Real.pi * Complex.I * (jf h : ℕ) / (M : ℂ)) := by
    intro h
    rw [zTriple, stdAddChar_triple, hMdef, exp_kFreq_mod _ _ hMpos]
  have hW : ∀ h, h ≠ 0 → ‖∑ m ∈ Finset.Icc 1 L, zTriple h ^ m‖ ≤ φ M (jf h) := by
    intro h hh
    rw [hz]
    exact norm_sum_Icc_pow_le (norm_exp_root M (jf h)).le
      (exp_root_ne_one (hjf_pos h hh) (hjf_lt h)) L
  -- expansion
  have hexp : ∑ m ∈ Finset.Icc 1 L, A₁ (m : ZMod n₁) * A₂ (m : ZMod n₂) * B (m : ZMod n₃) =
      ((M : ℕ) : ℂ)⁻¹ * ∑ h, C h * ∑ m ∈ Finset.Icc 1 L, zTriple h ^ m := by
    simp_rw [triple_expansion A₁ A₂ B, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun h _ => (Finset.mul_sum _ _ _).symm
  rw [hexp, norm_mul, norm_inv, Complex.norm_natCast]
  have hsplit : ∑ h, C h * ∑ m ∈ Finset.Icc 1 L, zTriple h ^ m =
      C 0 * L + ∑ h ∈ Finset.univ.erase 0, C h * ∑ m ∈ Finset.Icc 1 L, zTriple h ^ m := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]
    congr 1
    simp [zTriple]
  rw [hsplit]
  -- bound the nonzero frequencies
  have hS : ‖∑ h ∈ Finset.univ.erase 0, C h * ∑ m ∈ Finset.Icc 1 L, zTriple h ^ m‖ ≤
      α₁ * α₂ * βg * (M * (1 + Real.log M)) + α₁ * α₂ * βa * (M' * (1 + Real.log M')) := by
    set S₁ := (Finset.univ.erase (0 : ZMod n₁ × ZMod n₂ × ZMod n₃)).filter
      (fun h => ¬ d ∣ h.2.2.val) with hS₁
    set S₂ := (Finset.univ.erase (0 : ZMod n₁ × ZMod n₂ × ZMod n₃)).filter
      (fun h => d ∣ h.2.2.val) with hS₂
    have hbound : ∀ h ∈ Finset.univ.erase (0 : ZMod n₁ × ZMod n₂ × ZMod n₃),
        ‖C h * ∑ m ∈ Finset.Icc 1 L, zTriple h ^ m‖ ≤
          (if d ∣ h.2.2.val then α₁ * α₂ * βa else α₁ * α₂ * βg) * φ M (jf h) := by
      intro h hh
      have hh0 : h ≠ 0 := Finset.ne_of_mem_erase hh
      rw [norm_mul]
      refine mul_le_mul ?_ (hW h hh0) (norm_nonneg _) ?_
      · simp only [hC, norm_mul]
        split_ifs with hdv
        · exact mul_le_mul (mul_le_mul (hA₁ _) (hA₂ _) (norm_nonneg _) hα₁) (hBa _)
            (norm_nonneg _) (mul_nonneg hα₁ hα₂)
        · exact mul_le_mul (mul_le_mul (hA₁ _) (hA₂ _) (norm_nonneg _) hα₁) (hBg _ hdv)
            (norm_nonneg _) (mul_nonneg hα₁ hα₂)
      · split_ifs with hdv
        · exact mul_nonneg (mul_nonneg hα₁ hα₂) hβa
        · exact mul_nonneg (mul_nonneg hα₁ hα₂) ((norm_nonneg _).trans (hBg _ hdv))
    have hφnn : ∀ N j, 0 ≤ φ N j := fun N j => by simp only [hφ]; positivity
    -- the two frequency sums
    have hT₁ : ∑ h ∈ S₁, φ M (jf h) ≤ M * (1 + Real.log M) := by
      have hinj : Set.InjOn jf ↑S₁ := fun h _ h' _ he => hjf_inj h h' he
      rw [← Finset.sum_image hinj]
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (t := Finset.Ioo 0 M) ?_
        (fun j _ _ => hφnn M j)) ?_
      · intro j hj
        obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hj
        have hh0 : h ≠ 0 := Finset.ne_of_mem_erase (Finset.mem_filter.1 hh).1
        exact Finset.mem_Ioo.2 ⟨hjf_pos h hh0, hjf_lt h⟩
      · exact sum_two_div_norm_exp_sub_one_le M
    have hT₂ : ∑ h ∈ S₂, φ M (jf h) ≤ M' * (1 + Real.log M') := by
      have hinj : Set.InjOn jf ↑S₂ := fun h _ h' _ he => hjf_inj h h' he
      rw [← Finset.sum_image hinj]
      have hdinj : Set.InjOn (fun i => d * i) ↑(Finset.Ioo 0 M') :=
        fun i _ i' _ he => Nat.eq_of_mul_eq_mul_left hd0 he
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (t := (Finset.Ioo 0 M').image
        (fun i => d * i)) ?_ (fun j _ _ => hφnn M j)) ?_
      · intro j hj
        obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hj
        have hh0 : h ≠ 0 := Finset.ne_of_mem_erase (Finset.mem_filter.1 hh).1
        have hdh : d ∣ h.2.2.val := (Finset.mem_filter.1 hh).2
        have hdK : d ∣ kFreq n₁ n₂ n₃ h := by
          simp only [kFreq]
          refine dvd_add (dvd_add ?_ ?_) ?_
          · exact Dvd.dvd.mul_left (Dvd.dvd.mul_left (hdN ▸ dvd_mul_right d N₃) _) _
          · exact Dvd.dvd.mul_left (Dvd.dvd.mul_left (hdN ▸ dvd_mul_right d N₃) _) _
          · exact Dvd.dvd.mul_right hdh _
        have hdj : d ∣ jf h := (Nat.dvd_mod_iff (hMM' ▸ dvd_mul_right d M')).2 hdK
        obtain ⟨i, hi⟩ := hdj
        refine Finset.mem_image.2 ⟨i, Finset.mem_Ioo.2 ⟨?_, ?_⟩, hi.symm⟩
        · rcases Nat.eq_zero_or_pos i with h' | h'
          · have := hjf_pos h hh0; rw [hi, h', mul_zero] at this; exact absurd this (lt_irrefl 0)
          · exact h'
        · have := hjf_lt h
          rw [hi, hMM'] at this
          exact Nat.lt_of_mul_lt_mul_left this
      · rw [Finset.sum_image hdinj]
        have heq : ∀ i ∈ Finset.Ioo 0 M', φ M (d * i) = φ M' i := by
          intro i _
          simp only [hφ]
          congr 3
          have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
          rw [hMM']
          push_cast
          field_simp
        rw [Finset.sum_congr rfl heq]
        exact sum_two_div_norm_exp_sub_one_le M'
    calc ‖∑ h ∈ Finset.univ.erase 0, C h * ∑ m ∈ Finset.Icc 1 L, zTriple h ^ m‖
        ≤ ∑ h ∈ Finset.univ.erase 0, ‖C h * ∑ m ∈ Finset.Icc 1 L, zTriple h ^ m‖ :=
          norm_sum_le _ _
      _ ≤ ∑ h ∈ Finset.univ.erase 0,
          (if d ∣ h.2.2.val then α₁ * α₂ * βa else α₁ * α₂ * βg) * φ M (jf h) :=
          Finset.sum_le_sum hbound
      _ = α₁ * α₂ * βg * ∑ h ∈ S₁, φ M (jf h) + α₁ * α₂ * βa * ∑ h ∈ S₂, φ M (jf h) := by
          rw [← Finset.sum_filter_not_add_sum_filter _ (fun h => d ∣ h.2.2.val)]
          rw [Finset.mul_sum, Finset.mul_sum]
          congr 1
          · exact Finset.sum_congr rfl fun h hh => by rw [if_neg (Finset.mem_filter.1 hh).2]
          · exact Finset.sum_congr rfl fun h hh => by rw [if_pos (Finset.mem_filter.1 hh).2]
      _ ≤ α₁ * α₂ * βg * (M * (1 + Real.log M)) + α₁ * α₂ * βa * (M' * (1 + Real.log M')) := by
          have : 0 ≤ α₁ * α₂ * βg := mul_nonneg (mul_nonneg hα₁ hα₂) hβg
          have : 0 ≤ α₁ * α₂ * βa := mul_nonneg (mul_nonneg hα₁ hα₂) hβa
          gcongr
  have h1 : ‖C 0 * (L : ℂ) + ∑ h ∈ Finset.univ.erase 0, C h * ∑ m ∈ Finset.Icc 1 L, zTriple h ^ m‖
      ≤ c₀ * L + (α₁ * α₂ * βg * (M * (1 + Real.log M)) +
        α₁ * α₂ * βa * (M' * (1 + Real.log M'))) := by
    refine (norm_add_le _ _).trans (add_le_add ?_ hS)
    rw [norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_right h0 (Nat.cast_nonneg L)
  have hMR' : (M : ℝ) = d * M' := by rw [hMM']; push_cast; ring
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd0
  have hM'R : (0 : ℝ) < M' := by exact_mod_cast hM'pos
  calc (M : ℝ)⁻¹ * ‖C 0 * (L : ℂ) +
        ∑ h ∈ Finset.univ.erase 0, C h * ∑ m ∈ Finset.Icc 1 L, zTriple h ^ m‖
      ≤ (M : ℝ)⁻¹ * (c₀ * L + (α₁ * α₂ * βg * (M * (1 + Real.log M)) +
        α₁ * α₂ * βa * (M' * (1 + Real.log M')))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (L : ℝ) / M * c₀ + α₁ * α₂ * βg * (1 + Real.log M) +
        α₁ * α₂ * βa / d * (1 + Real.log M') := by
        rw [hMR']
        field_simp
        ring

end

end GaloisForLFunctions.RHTower.RootOfUnityCompletion
