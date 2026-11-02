import GaloisForLFunctions.WindowTowerOfSpecZ.TheWindowDirichletAlgebra
import GaloisForLFunctions.RHTower.MFreeLadder

/-!
# The symmetries of the tower

Two operations move windows and act on their algebras.

**Dilation and the Adams lifts (`A ↦ eA`).** Dilating the scaling line by `e ≥ 1`,
`(D_e H)(u) = H(u/e)`, maps the window of length `A` onto the window of length `eA` and the shift
by `t` onto the shift by `et` (`windowShift_dilate`). On the algebras it is the Adams lift
`ψ^e = mPart e` (the power dilation `f ↦ (n^e ↦ f(n))`, a ring endomorphism of the Dirichlet ring,
RHTower `powerDilationRingHom`):

`ρ_{eA}(ψ^e f) D_e = D_e ρ_A(f·n^{−(e−1)/2})` (`windowRepFun_mPart_dilate`).

So the tower is self-similar up to a Tate twist by `(e − 1)/2`: the window of length `eA` contains a
dilated copy of the window of length `A` whose arithmetic is carried by the `e`-th powers. Weil's
form is not self-similar: the longer window also sees every integer `≤ e^{eA}` that is not an
`e`-th power, and the Gamma factor is not dilation invariant. This is the analogue of base change
`𝔽_q ⇝ 𝔽_{q^e}` for the windows of a curve (ACS `TheTowersOfACurveAreItsBaseChanges`), where the
Frobenius orbit is exactly self-similar.

**Reflection and the Rosati involution.** The window involution `σ_A H(u) = H(−A − u)` (Serre duality
of a window, CWS) conjugates the window shift into its adjoint, the shift toward the left end cut at
`−A` (`windowInvolution_windowShift`, `integral_windowShift_mul_eq`):

`σ_A T_t σ_A = T_t^*`, `⟨T_t H, K⟩ = ⟨H, T_t^* K⟩`,

hence `σ_A ρ_A(f) σ_A = ρ_A(f)^*` (`integral_windowRepFun_mul_eq`): Serre duality is the Rosati
involution of the window algebra, and Weil's arithmetic term `−2⟨ρ_A(Λ)H, H⟩ =
−⟨(ρ_A(Λ) + σ_Aρ_A(Λ)σ_A)H, H⟩` is the Rosati symmetrization of the von Mangoldt operator.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.WindowTowerOfSpecZ

open CohomologyOfWindowsOfSpecZ

/-! ### Dilation and the Adams lifts -/

/-- The dilation `(D_r H)(u) = H(u / r)`. -/
def dilate (r : ℝ) (H : ℝ → ℝ) : ℝ → ℝ := fun u => H (u / r)

theorem dilate_mem {A r : ℝ} (hr : 0 < r) {H : ℝ → ℝ} (hH : H ∈ windowSupported A) :
    dilate r H ∈ windowSupported (r * A) := fun y hy => hH _ fun hm => hy ⟨by
  have := (le_div_iff₀ hr).mp hm.1; linarith, by
  have := (div_le_iff₀ hr).mp hm.2; linarith⟩

/-- **Dilation carries shifts to dilated shifts**: `T_{rt} D_r = D_r T_t`. -/
theorem windowShift_dilate {r : ℝ} (hr : 0 < r) (t : ℝ) (H : ℝ → ℝ) :
    windowShift (r * t) (dilate r H) = dilate r (windowShift t H) := by
  funext u
  rcases le_or_gt u 0 with hu | hu
  · rw [windowShift_apply_of_le _ hu, dilate, dilate,
      windowShift_apply_of_le _ (div_nonpos_of_nonpos_of_nonneg hu hr.le)]
    congr 1
    field_simp
  · rw [windowShift_apply_of_pos _ hu, dilate, windowShift_apply_of_pos _ (div_pos hu hr)]

/-- `n^e ≤ ⌊e^{eA}⌋` iff `n ≤ ⌊e^A⌋`. -/
theorem pow_le_windowLevel_iff {A : ℝ} {e n : ℕ} (he : 1 ≤ e) :
    n ^ e ≤ windowLevel (e * A) ↔ n ≤ windowLevel A := by
  have he0 : (0 : ℝ) < e := by exact_mod_cast he
  rw [windowLevel, windowLevel, Nat.le_floor_iff (Real.exp_pos _).le,
    Nat.le_floor_iff (Real.exp_pos _).le, Nat.cast_pow,
    show Real.exp (e * A) = Real.exp A ^ e by rw [← Real.exp_nat_mul]]
  exact pow_le_pow_iff_left₀ (Nat.cast_nonneg n) (Real.exp_pos A).le (by omega)

/-- **The tower is self-similar up to a Tate twist**:
`ρ_{eA}(ψ^e f) D_e H = D_e ρ_A(f·n^{−(e−1)/2}) H`. -/
theorem windowRepFun_mPart_dilate {A : ℝ} {e : ℕ} (he : 1 ≤ e) (f : ArithmeticFunction ℝ)
    (H : ℝ → ℝ) :
    windowRepFun (e * A) (RHTower.mPart e f) (dilate e H) =
      dilate e (windowRepFun A (tateTwist ((e - 1) / 2) f) H) := by
  funext u
  have he0 : (0 : ℝ) < e := by exact_mod_cast he
  have he' : e ≠ 0 := by omega
  set F : ℕ → ℝ := fun N => RHTower.mPart e f N / Real.sqrt N *
    windowShift (Real.log N) (dilate e H) u with hF
  -- only `e`-th powers contribute, and they are the images of the integers `≤ e^A`
  have hsub : (Finset.Icc 1 (windowLevel A)).image (fun n => n ^ e) ⊆
      Finset.Icc 1 (windowLevel (e * A)) := by
    intro N hN
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hN
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
    exact Finset.mem_Icc.mpr ⟨Nat.one_le_pow _ _ h1, (pow_le_windowLevel_iff he).mpr h2⟩
  have hzero : ∀ N ∈ Finset.Icc 1 (windowLevel (e * A)),
      N ∉ (Finset.Icc 1 (windowLevel A)).image (fun n => n ^ e) → F N = 0 := by
    intro N hN hnot
    rw [hF]
    simp only
    rw [RHTower.mPart_apply_of_forall_pow_ne e f fun k hk => hnot ?_, zero_div, zero_mul]
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hN
    refine Finset.mem_image.mpr ⟨k, Finset.mem_Icc.mpr ⟨?_, ?_⟩, hk⟩
    · rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [zero_pow he'] at hk; omega
      · exact hk0
    · exact (pow_le_windowLevel_iff he).mp (hk ▸ h2)
  rw [windowRepFun, ← Finset.sum_subset hsub hzero,
    Finset.sum_image fun a _ b _ hab => Nat.pow_left_injective he' hab, dilate, windowRepFun]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  rw [hF]
  simp only
  rw [RHTower.mPart_apply_pow he', Nat.cast_pow, Real.log_pow, windowShift_dilate he0,
    dilate, tateTwist_apply]
  -- `n^{−e/2} = n^{−(e−1)/2} · n^{−1/2}`
  have hsq : Real.sqrt ((n : ℝ) ^ e) = (n : ℝ) ^ ((e : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    ring_nf
  have hsq1 : Real.sqrt n = (n : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow n
  rw [hsq, hsq1, div_eq_mul_inv, div_eq_mul_inv, ← Real.rpow_neg hn0.le,
    ← Real.rpow_neg hn0.le, mul_assoc (f n), ← Real.rpow_add hn0]
  ring_nf

/-! ### Reflection and the Rosati involution -/

/-- The adjoint window shift `(T_t^* H)(u) = 1_{u ≥ −A} H(u + t)`. -/
def adjointShift (A t : ℝ) (H : ℝ → ℝ) : ℝ → ℝ := (Ici (-A)).indicator fun u => H (u + t)

/-- **Serre duality conjugates a shift into its adjoint**: `σ_A T_t σ_A = T_t^*`. -/
theorem windowInvolution_windowShift (A t : ℝ) (H : ℝ → ℝ) :
    windowInvolution A (windowShift t (windowInvolution A H)) = adjointShift A t H := by
  funext u
  simp only [windowInvolution, adjointShift]
  rcases le_or_gt (-A - u) 0 with hu | hu
  · rw [windowShift_apply_of_le _ hu, indicator_of_mem (mem_Ici.mpr (by linarith))]
    congr 1; ring
  · rw [windowShift_apply_of_pos _ hu, indicator_of_notMem (fun h => by
      linarith [mem_Ici.mp h])]

/-- `⟨T_t H, K⟩ = ⟨H, T_t^* K⟩` on window functions. -/
theorem integral_windowShift_mul_eq {A t : ℝ} {H K : ℝ → ℝ} (hH : H ∈ windowSupported A)
    (hK : K ∈ windowSupported A) :
    ∫ u, windowShift t H u * K u = ∫ u, H u * adjointShift A t K u := by
  have h1 : (fun u => windowShift t H u * K u) = fun u => H (u - t) * K u := funext fun u => by
    rcases le_or_gt u 0 with hu | hu
    · rw [windowShift_apply_of_le _ hu]
    · rw [windowShift_apply_of_pos _ hu, hK u fun hm => by linarith [hm.2], mul_zero, mul_zero]
  have h2 : (fun u => H u * adjointShift A t K u) = fun u => H u * K (u + t) := funext fun u => by
    simp only [adjointShift]
    rcases le_or_gt (-A) u with hu | hu
    · rw [indicator_of_mem (mem_Ici.mpr hu)]
    · rw [indicator_of_notMem (fun h => by linarith [mem_Ici.mp h]),
        hH u fun hm => by linarith [hm.1], zero_mul, zero_mul]
  rw [h1, h2, ← integral_sub_right_eq_self (fun u => H u * K (u + t)) t]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [sub_add_cancel]

/-- **Serre duality is the Rosati involution of the window algebra**:
`⟨ρ_A(f)H, K⟩ = ⟨H, σ_A ρ_A(f) σ_A K⟩` for integrable window functions. -/
theorem integral_windowRepFun_mul_eq {A : ℝ} (f : ArithmeticFunction ℝ) {H K : ℝ → ℝ}
    (hH : H ∈ windowSupported A) (hK : K ∈ windowSupported A)
    (hint : ∀ t : ℝ, Integrable fun u => windowShift t H u * K u)
    (hint' : ∀ t : ℝ, Integrable fun u => H u * adjointShift A t K u) :
    ∫ u, windowRepFun A f H u * K u =
      ∫ u, H u * windowInvolution A
        (windowRepFun A f (windowInvolution A K)) u := by
  have hσ : windowInvolution A (windowRepFun A f (windowInvolution A K)) = fun u =>
      ∑ n ∈ Finset.Icc 1 (windowLevel A), f n / Real.sqrt n * adjointShift A (Real.log n) K u := by
    funext u
    simp only [windowInvolution, windowRepFun]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← windowInvolution_windowShift A (Real.log n) K]
    rfl
  rw [hσ]
  simp_rw [windowRepFun, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [integral_finsetSum _ fun n _ => (hint _).const_mul _,
    integral_finsetSum _ fun n _ => by
      simp_rw [mul_left_comm (H _)]; exact (hint' _).const_mul _]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [integral_const_mul, integral_windowShift_mul_eq hH hK]
  simp_rw [mul_left_comm (H _)]
  rw [integral_const_mul]

end GaloisForLFunctions.WindowTowerOfSpecZ
