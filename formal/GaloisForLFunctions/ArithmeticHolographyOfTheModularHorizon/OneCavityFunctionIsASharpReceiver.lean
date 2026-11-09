import GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon.TheTwoModeEnergiesRingDownAtTheZeroFreeRate

/-!
# One cavity function is a sharp receiver

The two-mode theorem needs a family of states. This module builds **one** cuspidal function of Maass cusp forms
whose energy is a sharp receiver: its horocycle ringdown rate is exactly the zero-free region of `ζ`.

**Uniform pair bounds.** For every pair of cuspidal eigenforms `v_j, v_k` the polar transform of `v_j v̄_k` on
`Re s = 5/4` is at most `D_{jk} (1 + |t|)^N e^{−π|t|}` with one exponent `N = 4N_Γ + 3` for all pairs
(`pairPolar_right_bound`).

**Normalizers.** Put `M_j = max(1, M_j⁰)(1 + Σ_{m ≤ j} (D_{jm} + D_{mj}))` (`normM`), so that `‖v_j‖ ≤ M_j e^{−π Im z}`
and `D_{jk} ≤ M_j M_k` (`pairD_le`). For the cavity function `g_x = Σ_j x_j 2^{−j} v_j/M_j` the energy expands as the
double series `Σ_{j,k} x_j x̄_k 2^{−j−k} v_j v̄_k/(M_j M_k)`; integrating term by term,
`|P_{|g_x|²}(5/4 + it)| ≤ 4‖x‖² (1 + |t|)^N e^{−π|t|}` (`cavity_polar_right`). By the ringdown theorem for seeds the
energy rings down at the zero-free rate.

**The sharp receiver** (`exists_sharp_cavity_receiver`). For a Baire-generic `x` the function `g = g_x` is cuspidal,
sees every right resonance (pairwise visibility), and

* RH ⟺ `|a_{|g|²}(y) − c| ≤ C y^{3/4−ε}` for every `ε > 0`;
* a zero-free strip `Re z > 1 − δ` ⟺ a rate `y^α` with `α > ½`.
-/

open Complex MeasureTheory Set Filter Topology BoundedContinuousFunction
open scoped MatrixGroups UpperHalfPlane

noncomputable section

namespace GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon

open _root_.RHTower GaloisForLFunctions.HTGeometry GaloisForLFunctions.BlackHoleRingdown
open GaloisForLFunctions.RHTower.DeckPointPair (CuspEigenIndex)

/-! ### The enumerated eigenbasis and its constants -/

/-- An enumeration of the cuspidal eigenbasis. -/
def maassEnum : ℕ → CuspEigenIndex 0 :=
  haveI := countable_cuspEigenIndex
  haveI : Nonempty (CuspEigenIndex 0) := by haveI := infinite_cuspEigenIndex; infer_instance
  (exists_surjective_nat (CuspEigenIndex 0)).choose

theorem maassEnum_surjective : Function.Surjective maassEnum :=
  haveI := countable_cuspEigenIndex
  haveI : Nonempty (CuspEigenIndex 0) := by haveI := infinite_cuspEigenIndex; infer_instance
  (exists_surjective_nat (CuspEigenIndex 0)).choose_spec

/-- The `n`-th cuspidal eigenform. -/
def mv (n : ℕ) : ℍ → ℂ := maassForm (maassEnum n)

theorem mv_mem (n : ℕ) : mv n ∈ HeckeCusp.cuspSpace (maassEnum n).1 := maassForm_mem _

/-- Whittaker coefficients of `v_n`. -/
def mρ (n : ℕ) : ℤ → ℂ := (CuspL.exists_whittaker (mv_mem n)).choose

theorem mρ_zero (n : ℕ) : mρ n 0 = 0 := (CuspL.exists_whittaker (mv_mem n)).choose_spec.1

theorem mρ_spec (n : ℕ) : ∀ k : ℤ, ∀ y, 0 < y → HeckeCusp.fourierCoeff (mv n) k y =
    mρ n k * (Real.sqrt y : ℂ) * modifiedBesselKOrder (2 * Real.pi * |(k : ℝ)| * y) (CuspL.nu (maassEnum n).1) :=
  (CuspL.exists_whittaker (mv_mem n)).choose_spec.2

/-- The Gamma constant on the line `Re = 5/8`. -/
theorem gammaData : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ y : ℝ, ‖Gamma (((5 / 8 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
    C * (1 + |y|) ^ N * Real.exp (-(Real.pi * |y| / 2)) :=
  _root_.RHTower.exists_bound_norm_Gamma_vertical_line (5 / 8) (by norm_num)

def gC : ℝ := gammaData.choose
def gN : ℕ := gammaData.choose_spec.choose
theorem gC_nonneg : 0 ≤ gC := gammaData.choose_spec.choose_spec.1
theorem gC_spec : ∀ y : ℝ, ‖Gamma (((5 / 8 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
    gC * (1 + |y|) ^ gN * Real.exp (-(Real.pi * |y| / 2)) := gammaData.choose_spec.choose_spec.2

/-- The pair constant `D_{jk}` on the line `Re s = 5/4`. -/
def pairD (j k : ℕ) : ℝ :=
  (pairPolar_right_bound gC_nonneg gC_spec (mv_mem j) (mv_mem k) (mρ_zero j) (mρ_spec j) (mρ_zero k)
    (mρ_spec k)).choose

theorem pairD_nonneg (j k : ℕ) : 0 ≤ pairD j k :=
  (pairPolar_right_bound gC_nonneg gC_spec (mv_mem j) (mv_mem k) (mρ_zero j) (mρ_spec j) (mρ_zero k)
    (mρ_spec k)).choose_spec.1

theorem pairD_spec (j k : ℕ) : ∀ s : ℂ, s.re = 5 / 4 → 1 ≤ |s.im| →
    ‖polarTransform (fun z => mv j z * starRingEnd ℂ (mv k z)) s‖ ≤
      pairD j k * (1 + |s.im|) ^ (4 * gN + 3) * Real.exp (-(Real.pi * |s.im|)) :=
  (pairPolar_right_bound gC_nonneg gC_spec (mv_mem j) (mv_mem k) (mρ_zero j) (mρ_spec j) (mρ_zero k)
    (mρ_spec k)).choose_spec.2

/-- The envelope constant of `v_n`, at least `1`. -/
def envM (n : ℕ) : ℝ := max 1 (exists_envelope_of_mem_cuspSpace (mv_mem n)).choose

theorem one_le_envM (n : ℕ) : 1 ≤ envM n := le_max_left _ _

theorem envM_spec (n : ℕ) (z : ℍ) : ‖mv n z‖ ≤ envM n * Real.exp (-Real.pi * z.im) :=
  ((exists_envelope_of_mem_cuspSpace (mv_mem n)).choose_spec.2 z).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)

/-- `E_n = Σ_{m ≤ n} (D_{nm} + D_{mn})`. -/
def pairE (n : ℕ) : ℝ := ∑ m ∈ Finset.range (n + 1), (pairD n m + pairD m n)

theorem pairE_nonneg (n : ℕ) : 0 ≤ pairE n :=
  Finset.sum_nonneg fun _ _ => add_nonneg (pairD_nonneg _ _) (pairD_nonneg _ _)

/-- The normalizers `M_n = envM_n (1 + E_n)`. -/
def normM (n : ℕ) : ℝ := envM n * (1 + pairE n)

theorem one_le_normM (n : ℕ) : 1 ≤ normM n := by
  have := one_le_envM n; have := pairE_nonneg n
  unfold normM; nlinarith

theorem normM_spec (n : ℕ) (z : ℍ) : ‖mv n z‖ ≤ normM n * Real.exp (-Real.pi * z.im) := by
  refine (envM_spec n z).trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
  have := one_le_envM n; have := pairE_nonneg n
  unfold normM; nlinarith

theorem pairD_le_pairE {j k : ℕ} (hkj : k ≤ j) : pairD j k ≤ pairE j := by
  have h := Finset.single_le_sum (f := fun m => pairD j m + pairD m j)
    (fun m _ => add_nonneg (pairD_nonneg _ _) (pairD_nonneg _ _))
    (Finset.mem_range.2 (Nat.lt_succ_of_le hkj))
  have := pairD_nonneg k j
  unfold pairE; linarith

theorem pairD_le_pairE' {j k : ℕ} (hjk : j ≤ k) : pairD j k ≤ pairE k := by
  have h := Finset.single_le_sum (f := fun m => pairD k m + pairD m k)
    (fun m _ => add_nonneg (pairD_nonneg _ _) (pairD_nonneg _ _))
    (Finset.mem_range.2 (Nat.lt_succ_of_le hjk))
  have := pairD_nonneg k j
  unfold pairE; linarith

/-- **`D_{jk} ≤ M_j M_k`.** -/
theorem pairD_le (j k : ℕ) : pairD j k ≤ normM j * normM k := by
  have hj := one_le_normM j
  have hk := one_le_normM k
  have hEj : 1 + pairE j ≤ normM j := by
    have := one_le_envM j; have := pairE_nonneg j; unfold normM; nlinarith
  have hEk : 1 + pairE k ≤ normM k := by
    have := one_le_envM k; have := pairE_nonneg k; unfold normM; nlinarith
  rcases le_total k j with h | h
  · have := pairD_le_pairE h; nlinarith
  · have := pairD_le_pairE' h; nlinarith

theorem normM_hyp : ∀ n, 0 < normM n ∧ ∀ z : ℍ, ‖mv n z‖ ≤ normM n * Real.exp (-Real.pi * z.im) :=
  fun n => ⟨lt_of_lt_of_le one_pos (one_le_normM n), normM_spec n⟩

theorem isCavityFamily_sharp : IsCavityFamily (cuspFamily mv normM) Real.pi :=
  isCavityFamily_cuspFamily mv_mem normM_hyp

/-! ### The polar transform of the cavity energy -/

theorem isSeed_member {u : ℕ → ℍ → ℂ} {κ : ℝ} (hu : IsCavityFamily u κ) (j : ℕ) : IsSeed (u j) := by
  refine ⟨hu.invariant j, hu.continuous j, ⟨1, fun z => (hu.envelope j z).trans ?_⟩,
    ⟨1, κ, zero_le_one, hu.pos, fun z _ => by rw [one_mul]; exact hu.envelope j z⟩⟩
  exact Real.exp_le_one_iff.2 (by nlinarith [hu.pos, z.im_pos])

/-- **The cavity energy on `Re s = 5/4`**: `|P_{|g_x|²}(s)| ≤ 4‖x‖² (1 + |t|)^N e^{−π|t|}`. -/
theorem cavity_polar_right (x : ℕ →ᵇ ℂ) {s : ℂ} (hs : s.re = 5 / 4) (ht : 1 ≤ |s.im|) :
    ‖polarTransform (fun z => ((‖cavity (cuspFamily mv normM) x z‖ ^ 2 : ℝ) : ℂ)) s‖ ≤
      4 * ‖x‖ ^ 2 * (1 + |s.im|) ^ (4 * gN + 3) * Real.exp (-(Real.pi * |s.im|)) := by
  set u := cuspFamily mv normM
  have hu := isCavityFamily_sharp
  set K : ℍ → ℂ := fun z => polarNumerator (s - 1 / 2) z.re z.im
  set f : ℕ → ℍ → ℂ := fun j z => x j * (wt j : ℂ) * u j z
  set Q := (1 + |s.im|) ^ (4 * gN + 3) * Real.exp (-(Real.pi * |s.im|))
  have hQ : 0 ≤ Q := by positivity
  have hfs : ∀ z, Summable fun j => ‖f j z‖ := fun z =>
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => norm_cavityTerm_le hu x j z)
      (summable_wt.mul_left _)
  have hfs' : ∀ z, Summable fun j => ‖starRingEnd ℂ (f j z)‖ := fun z => by
    simpa only [Complex.norm_conj] using hfs z
  -- the energy as a double series
  have hE : ∀ z, ((‖cavity u x z‖ ^ 2 : ℝ) : ℂ) * K z =
      ∑' p : ℕ × ℕ, f p.1 z * starRingEnd ℂ (f p.2 z) * K z := by
    intro z
    rw [Complex.ofReal_pow, ← Complex.mul_conj', cavity, Complex.conj_tsum,
      tsum_mul_tsum_of_summable_norm (hfs z) (hfs' z), ← tsum_mul_right]
  -- integrability of the terms
  obtain ⟨α, β, a, hα, hβ, ha, hK⟩ := exists_polar_bound (K := {s - 1 / 2}) isCompact_singleton
  have hKb : ∀ (x' Y : ℝ), 1 / 2 ≤ Y → ‖polarNumerator (s - 1 / 2) x' Y‖ ≤ α * Y ^ a + β :=
    fun x' Y hY => hK _ (mem_singleton _) x' Y hY
  have hterm_eq : ∀ (p : ℕ × ℕ) (z : ℍ), f p.1 z * starRingEnd ℂ (f p.2 z) * K z =
      (x p.1 * (wt p.1 : ℂ) * starRingEnd ℂ (x p.2 * (wt p.2 : ℂ))) *
        ((u p.1 z * starRingEnd ℂ (u p.2 z)) * K z) := by
    intro p z; simp only [f, map_mul]; ring
  have hint : ∀ p : ℕ × ℕ, Integrable (fun z => f p.1 z * starRingEnd ℂ (f p.2 z) * K z)
      (volume.restrict ModularGroup.fd) := by
    intro p
    have h := integrableOn_kernel ((isSeed_member hu p.1).mul (isSeed_member hu p.2).star)
      (continuous_polarNumerator_max (s - 1 / 2)) hα hβ ha hKb
    exact (h.const_mul (x p.1 * (wt p.1 : ℂ) * starRingEnd ℂ (x p.2 * (wt p.2 : ℂ)))).congr
      (Eventually.of_forall fun z => (hterm_eq p z).symm)
  obtain ⟨B, hB0, hB⟩ := exists_rpow_mul_exp_le ha (c := 2 * Real.pi) (by positivity)
  set B' := α * B + β
  have hpt : ∀ p : ℕ × ℕ, ∀ z ∈ ModularGroup.fd,
      ‖f p.1 z * starRingEnd ℂ (f p.2 z) * K z‖ ≤ ‖x‖ ^ 2 * (wt p.1 * wt p.2) * B' := by
    intro p z hz
    have hz2 : 1 / 2 < z.im := OddCusp.half_lt_im_of_mem_fd hz
    have h1 := norm_cavityTerm_le hu x p.1 z
    have h2 := norm_cavityTerm_le hu x p.2 z
    have hk := hKb z.re z.im hz2.le
    have hb := hB z.im z.im_pos
    have he : Real.exp (-Real.pi * z.im) * Real.exp (-Real.pi * z.im) = Real.exp (-(2 * Real.pi) * z.im) := by
      rw [← Real.exp_add]; ring_nf
    have hle : Real.exp (-(2 * Real.pi) * z.im) * (α * z.im ^ a + β) ≤ B' := by
      have h1' : Real.exp (-(2 * Real.pi) * z.im) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos, z.im_pos])
      calc Real.exp (-(2 * Real.pi) * z.im) * (α * z.im ^ a + β)
          = α * (z.im ^ a * Real.exp (-(2 * Real.pi) * z.im)) + β * Real.exp (-(2 * Real.pi) * z.im) := by ring
        _ ≤ α * B + β * 1 := by gcongr
        _ = B' := by ring
    rw [norm_mul, norm_mul, Complex.norm_conj]
    have hw1 := (wt_pos p.1).le
    have hw2 := (wt_pos p.2).le
    have hA1 : 0 ≤ ‖x‖ * Real.exp (-Real.pi * z.im) * wt p.1 :=
      mul_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) hw1
    have hA2 : 0 ≤ ‖x‖ * Real.exp (-Real.pi * z.im) * wt p.2 :=
      mul_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) hw2
    calc ‖f p.1 z‖ * ‖f p.2 z‖ * ‖K z‖
        ≤ (‖x‖ * Real.exp (-Real.pi * z.im) * wt p.1) * (‖x‖ * Real.exp (-Real.pi * z.im) * wt p.2) *
            (α * z.im ^ a + β) :=
          mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) hA1) hk (norm_nonneg _) (mul_nonneg hA1 hA2)
      _ = ‖x‖ ^ 2 * (wt p.1 * wt p.2) *
            ((Real.exp (-Real.pi * z.im) * Real.exp (-Real.pi * z.im)) * (α * z.im ^ a + β)) := by ring
      _ ≤ ‖x‖ ^ 2 * (wt p.1 * wt p.2) * B' := by
          rw [he]; exact mul_le_mul_of_nonneg_left hle (mul_nonneg (sq_nonneg _) (mul_nonneg hw1 hw2))
  have hfin : (volume : Measure ℍ) ModularGroup.fd < ⊤ := by rw [volume_fd_eq]; exact ENNReal.ofReal_lt_top
  have hwt2 : Summable fun p : ℕ × ℕ => wt p.1 * wt p.2 :=
    Summable.mul_of_nonneg summable_wt summable_wt (fun j => (wt_pos j).le) (fun j => (wt_pos j).le)
  have hsum : Summable fun p : ℕ × ℕ => ∫ z in ModularGroup.fd, ‖f p.1 z * starRingEnd ℂ (f p.2 z) * K z‖ := by
    refine Summable.of_nonneg_of_le (fun p => integral_nonneg fun _ => norm_nonneg _) (fun p => ?_)
      ((hwt2.mul_left (‖x‖ ^ 2)).mul_right (B' * (Real.pi / 3)))
    have hpt' : ∀ z ∈ ModularGroup.fd, ‖‖f p.1 z * starRingEnd ℂ (f p.2 z) * K z‖‖ ≤
        ‖x‖ ^ 2 * (wt p.1 * wt p.2) * B' := fun z hz => by rw [norm_norm]; exact hpt p z hz
    have h := norm_setIntegral_le_of_norm_le_const hfin hpt'
    rw [volume_real_fd] at h
    calc _ ≤ ‖∫ z in ModularGroup.fd, ‖f p.1 z * starRingEnd ℂ (f p.2 z) * K z‖‖ := le_abs_self _
      _ ≤ ‖x‖ ^ 2 * (wt p.1 * wt p.2) * B' * (Real.pi / 3) := h
      _ = ‖x‖ ^ 2 * (wt p.1 * wt p.2) * (B' * (Real.pi / 3)) := by ring
  -- term by term
  have hP : polarTransform (fun z => ((‖cavity u x z‖ ^ 2 : ℝ) : ℂ)) s =
      ∑' p : ℕ × ℕ, ∫ z in ModularGroup.fd, f p.1 z * starRingEnd ℂ (f p.2 z) * K z := by
    rw [integral_tsum_of_summable_integral_norm hint hsum]
    unfold polarTransform
    exact setIntegral_congr_fun ModularGroup.isClosed_fd.measurableSet fun z _ => hE z
  have hterm : ∀ p : ℕ × ℕ, ‖∫ z in ModularGroup.fd, f p.1 z * starRingEnd ℂ (f p.2 z) * K z‖ ≤
      ‖x‖ ^ 2 * Q * (wt p.1 * wt p.2) := by
    intro p
    have e : ∫ z in ModularGroup.fd, f p.1 z * starRingEnd ℂ (f p.2 z) * K z =
        (x p.1 * (wt p.1 : ℂ) * starRingEnd ℂ (x p.2 * (wt p.2 : ℂ)) * ((normM p.1 : ℂ))⁻¹ *
          ((normM p.2 : ℂ))⁻¹) * polarTransform (fun z => mv p.1 z * starRingEnd ℂ (mv p.2 z)) s := by
      unfold polarTransform
      rw [← integral_const_mul]
      refine setIntegral_congr_fun ModularGroup.isClosed_fd.measurableSet fun z _ => ?_
      simp only [f, u, cuspFamily, K, map_mul, map_inv₀, Complex.conj_ofReal]
      ring
    rw [e, norm_mul]
    have hM1 := lt_of_lt_of_le one_pos (one_le_normM p.1)
    have hM2 := lt_of_lt_of_le one_pos (one_le_normM p.2)
    have hc : ‖x p.1 * (wt p.1 : ℂ) * starRingEnd ℂ (x p.2 * (wt p.2 : ℂ)) * ((normM p.1 : ℂ))⁻¹ *
        ((normM p.2 : ℂ))⁻¹‖ = ‖x p.1‖ * wt p.1 * (‖x p.2‖ * wt p.2) / (normM p.1 * normM p.2) := by
      simp only [norm_mul, norm_inv, Complex.norm_conj, Complex.norm_real,
        Real.norm_of_nonneg (wt_pos _).le, Real.norm_of_nonneg hM1.le, Real.norm_of_nonneg hM2.le]
      field_simp
    rw [hc]
    have hD := pairD_spec p.1 p.2 s hs ht
    have hDM := pairD_le p.1 p.2
    have hx1 := x.norm_coe_le_norm p.1
    have hx2 := x.norm_coe_le_norm p.2
    have hMM : 0 < normM p.1 * normM p.2 := mul_pos hM1 hM2
    have hw1 := (wt_pos p.1).le
    have hw2 := (wt_pos p.2).le
    have hcoef : 0 ≤ ‖x p.1‖ * wt p.1 * (‖x p.2‖ * wt p.2) / (normM p.1 * normM p.2) :=
      div_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) hw1) (mul_nonneg (norm_nonneg _) hw2)) hMM.le
    calc ‖x p.1‖ * wt p.1 * (‖x p.2‖ * wt p.2) / (normM p.1 * normM p.2) *
          ‖polarTransform (fun z => mv p.1 z * starRingEnd ℂ (mv p.2 z)) s‖
        ≤ ‖x p.1‖ * wt p.1 * (‖x p.2‖ * wt p.2) / (normM p.1 * normM p.2) * (pairD p.1 p.2 * Q) := by
          refine mul_le_mul_of_nonneg_left ?_ hcoef
          rw [show pairD p.1 p.2 * Q = pairD p.1 p.2 * (1 + |s.im|) ^ (4 * gN + 3) *
            Real.exp (-(Real.pi * |s.im|)) by simp only [Q]; ring]
          exact hD
      _ ≤ ‖x p.1‖ * wt p.1 * (‖x p.2‖ * wt p.2) / (normM p.1 * normM p.2) * (normM p.1 * normM p.2 * Q) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hDM hQ) hcoef
      _ = ‖x p.1‖ * ‖x p.2‖ * Q * (wt p.1 * wt p.2) := by field_simp
      _ ≤ ‖x‖ * ‖x‖ * Q * (wt p.1 * wt p.2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul hx1 hx2 (norm_nonneg _) (norm_nonneg _)) hQ) (mul_nonneg hw1 hw2)
      _ = ‖x‖ ^ 2 * Q * (wt p.1 * wt p.2) := by ring
  have hhas : HasSum (fun p : ℕ × ℕ => ‖x‖ ^ 2 * Q * (wt p.1 * wt p.2)) (‖x‖ ^ 2 * Q * (2 * 2)) :=
    (hasSum_geometric_two.mul hasSum_geometric_two hwt2).mul_left _
  rw [hP]
  refine (tsum_of_norm_bounded hhas hterm).trans_eq ?_
  ring

theorem exists_cavity_polar_decay (x : ℕ →ᵇ ℂ) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ s : ℂ, -1 / 4 ≤ s.re → s.re ≤ 5 / 4 →
      ‖polarTransform (fun z => ((‖cavity (cuspFamily mv normM) x z‖ ^ 2 : ℝ) : ℂ)) s‖ ≤
        C * (1 + |s.im|) ^ N * Real.exp (-(Real.pi * |s.im|)) :=
  exists_polarTransform_decay (isSeed_cavity isCavityFamily_sharp x).normSq
    ⟨4 * ‖x‖ ^ 2, 4 * gN + 3, by positivity, fun s hs ht => cavity_polar_right x hs ht⟩

/-! ### The sharp receiver -/

/-- **One cavity function is a sharp receiver.** There are an enumeration `v_n` of the cuspidal Laplace
eigenforms, normalizers `M_n > 0` and coefficients `x` such that the cuspidal function
`g = Σ_n x_n 2^{−n} v_n/M_n` satisfies: RH holds iff the energy `|g|²` converges on closed horocycles at rate
`y^{3/4−ε}` for every `ε > 0`, and `ζ` has a zero-free strip iff `|g|²` converges at some rate `y^α`, `α > ½`. -/
theorem exists_sharp_cavity_receiver :
    ∃ (v : ℕ → ℍ → ℂ) (lam : ℕ → ℝ) (M : ℕ → ℝ) (x : ℕ →ᵇ ℂ),
      (∀ n, v n ∈ HeckeCusp.cuspSpace (lam n)) ∧ (∀ n, 0 < M n) ∧
      (∀ y : ℝ, 0 < y → response (cavity (cuspFamily v M) x) y = 0) ∧
      (RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ (c : ℂ) (C : ℝ), ∀ y : ℝ, 0 < y → y ≤ 1 →
        ‖response (fun z => ((‖cavity (cuspFamily v M) x z‖ ^ 2 : ℝ) : ℂ)) y - c‖ ≤ C * y ^ (3 / 4 - ε)) ∧
      ((∃ δ : ℝ, 0 < δ ∧ ∀ z : ℂ, 1 - δ < z.re → riemannZeta z ≠ 0) ↔
        ∃ α : ℝ, 1 / 2 < α ∧ ∃ (c : ℂ) (C : ℝ), ∀ y : ℝ, 0 < y → y ≤ 1 →
          ‖response (fun z => ((‖cavity (cuspFamily v M) x z‖ ^ 2 : ℝ) : ℂ)) y - c‖ ≤ C * y ^ α) := by
  have hu := isCavityFamily_sharp
  -- a cavity function seeing every right resonance
  obtain ⟨x, hx⟩ := (cavity_sees_every_right_zero_iff hu).2 fun ρ hζ hρ => by
    obtain ⟨i, l, h⟩ := exists_maass_pair_seeing hζ (by linarith)
    obtain ⟨n, rfl⟩ := maassEnum_surjective l
    obtain ⟨m, rfl⟩ := maassEnum_surjective i
    refine ⟨n, m, ?_⟩
    rw [pairEntry_cuspFamily]
    have h1 : ((normM n : ℂ))⁻¹ ≠ 0 := inv_ne_zero (ofReal_ne_zero.2 (normM_hyp n).1.ne')
    have h2 : ((normM m : ℂ))⁻¹ ≠ 0 := inv_ne_zero (ofReal_ne_zero.2 (normM_hyp m).1.ne')
    exact mul_ne_zero (mul_ne_zero h1 h2) h
  have hF := (isSeed_cavity hu x).normSq
  have hdecay := exists_cavity_polar_decay x
  refine ⟨mv, fun n => (maassEnum n).1, normM, x, mv_mem, fun n => (normM_hyp n).1,
    fun y hy => response_cavity_cuspFamily_eq_zero mv_mem normM_hyp x hy, ⟨fun hRH ε hε => ?_, fun h => ?_⟩,
    ⟨fun ⟨δ, hδ, hzf⟩ => ?_, fun ⟨α, hα, c, C, hrate⟩ => ?_⟩⟩
  · set ε' := min ε (1 / 4)
    have hε' : 0 < ε' := lt_min hε (by norm_num)
    obtain ⟨C, hC, hr⟩ := response_rate_of_riemannHypothesis hRH hF hdecay hε'
      (by linarith [min_le_right ε (1 / 4)])
    refine ⟨_, C, fun y hy hy1 => (hr y hy hy1).trans ?_⟩
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hy hy1
      (by linarith [min_le_left ε (1 / 4)])) hC
  · refine riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re.2 fun s hs hζ => ?_
    obtain ⟨c, C, hr⟩ := h ((s.re - 1 / 2) / 4) (by linarith)
    have := re_le_of_cavity_rate hu hx hr hζ hs
    linarith
  · set Θ := max (1 - δ) (1 / 2)
    have hΘ : 1 / 2 ≤ Θ := le_max_right _ _
    have hΘ1 : Θ < 1 := max_lt (by linarith) (by norm_num)
    have hzfΘ : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0 := fun z hz =>
      hzf z (lt_of_le_of_lt (le_max_left _ _) hz)
    obtain ⟨C, -, hr⟩ := response_rate_of_zeroFree hF hdecay hΘ hΘ1.le hzfΘ (ε := (1 - Θ) / 4)
      (by linarith) (by linarith)
    exact ⟨1 - Θ / 2 - (1 - Θ) / 4, by linarith, _, C, hr⟩
  · refine ⟨min (2 * α - 1) (1 / 2), lt_min (by linarith) (by norm_num), fun z hz hζ => ?_⟩
    have h1 : 1 / 2 < z.re := by linarith [min_le_right (2 * α - 1) (1 / 2)]
    have h2 := re_le_of_cavity_rate hu hx hrate hζ h1
    linarith [min_le_left (2 * α - 1) (1 / 2)]

end GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon
