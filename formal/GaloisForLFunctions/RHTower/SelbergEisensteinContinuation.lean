import GaloisForLFunctions.RHTower.SelbergEisensteinDecomposition
import GaloisForLFunctions.RHTower.SelbergRamanujanZeroZero
import GaloisForLFunctions.RHTower.TotientMulLSeries
import GaloisForLFunctions.RHTower.SelbergEisensteinStar

open Complex UpperHalfPlane LSeries
open scoped FourierTransform LSeries.notation

/-!
# Meromorphic continuation of the `Γ(N)` Eisenstein series to `Re s > 1/2`

The `n = 0` Kloosterman terms are supported on `c ∈ Nℤ`, even in `c` (`cterm_neg`), and at `c = Nn` equal
`pref(s,z) · φ(N²n) n^{-2s}` (`cterm_nat`, from `S_N(0,0;Nn) φ(N) = φ(N²n)`). Hence their sum is
`2 pref(s,z) Σ_n φ(N²n) n^{-2s} = 2 pref(s,z) φ(N²) L(μχ_{N²}, 2s) ζ(2s-1)` (`tsum_cterm`, `constTerm`), and for
`N ≥ 3`, `Re s > 1`: `E(z,s) = y^s + constTerm(s,z) + E^*(z,s)` (`eisenstein_eq`). Both `constTerm(·,z)`
(`differentiableAt_constTerm`, on `Re s > 1/2`, `s ≠ 1`) and `E^*(·,z)` (on `Re s > 1/2`) are holomorphic there, so
`E(z,s) - y^s` continues meromorphically to `Re s > 1/2` with at most the pole of `ζ(2s-1)` at `s = 1`.
-/

namespace GaloisForLFunctions.RHTower.SelbergEisensteinContinuation
open GaloisForLFunctions.RHTower.SelbergPoincareKernel GaloisForLFunctions.RHTower.SelbergPoincareFourier
  GaloisForLFunctions.RHTower.SelbergEisensteinDecomposition GaloisForLFunctions.RHTower.SelbergRamanujanZeroZero
  GaloisForLFunctions.RHTower.TotientMulLSeries GaloisForLFunctions.RHTower.SelbergKloostermanCongruence
  GaloisForLFunctions.RHTower.SelbergEisensteinStar GaloisForLFunctions.RHTower.SelbergPoincareContinuation

variable (N : ℕ) [NeZero N]

omit [NeZero N] in
theorem ksum_zero_of_not_dvd {c : ℤ} (h : ¬ (N : ℤ) ∣ c) (m : ℕ) (n : ℤ) : ksum N m c n = 0 := by
  unfold ksum
  exact Finset.sum_eq_zero (fun r _ => Set.indicator_of_notMem (fun hm => h hm.1) _)

omit [NeZero N] in
theorem ksum_neg (c : ℤ) : ksum N 0 (-c) 0 = ksum N 0 c 0 := by
  unfold ksum
  rw [Int.natAbs_neg]
  apply Finset.sum_congr rfl
  intro r _
  have hmem : (-c, (r : ℤ)) ∈ adm N ↔ (c, (r : ℤ)) ∈ adm N := by
    simp only [adm, Set.mem_setOf_eq, dvd_neg, IsCoprime.neg_left_iff]
  by_cases h : (c, (r : ℤ)) ∈ adm N
  · rw [Set.indicator_of_mem (hmem.mpr h), Set.indicator_of_mem h]; simp [kphase, phase]
  · rw [Set.indicator_of_notMem (fun h' => h (hmem.mp h')), Set.indicator_of_notMem h]

omit [NeZero N] in
theorem cterm_neg (s : ℂ) (z : ℍ) (c : ℤ) : cterm N s z (-c) = cterm N s z c := by
  unfold cterm
  simp only [neg_eq_zero, Int.cast_neg, neg_sq, ksum_neg]

/-- The `s`-dependent prefactor of the constant term. -/
noncomputable def pref (s : ℂ) (z : ℍ) : ℂ :=
  cexp (-s * (Real.log ((N : ℝ) ^ 2) : ℂ)) * cexp (-s * (Real.log N : ℂ)) * 𝓕 (ker 0 (z.im / N) s) 0 /
    (Nat.totient N : ℂ)

theorem cterm_nat (s : ℂ) (z : ℍ) {n : ℕ} (hn : 0 < n) :
    cterm N s z ((N : ℤ) * n) = pref N s z * LSeries.term (fun k => (((N ^ 2) * k).totient : ℂ)) (2 * s) n := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hc : ((N : ℤ) * n) ≠ 0 := by positivity
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hφ : (Nat.totient N : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hN).ne'
  have hk := ksum_zero_zero N hc (Dvd.intro _ rfl)
  have hnat : ((N : ℤ) * n).natAbs * N = N ^ 2 * n := by
    rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast]; ring
  rw [hnat] at hk
  have hks : ksum N 0 ((N : ℤ) * n) 0 = (((N ^ 2 * n).totient : ℕ) : ℂ) / (Nat.totient N : ℂ) := by
    rw [eq_div_iff hφ]; exact hk
  unfold cterm pref
  rw [if_neg hc, hks, LSeries.term_of_ne_zero hn.ne']
  have hlog : Real.log ((((N : ℤ) * n : ℤ) : ℝ) ^ 2) = Real.log ((N : ℝ) ^ 2) + 2 * Real.log n := by
    push_cast
    rw [mul_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]; push_cast; ring
  rw [hlog]
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [cpow_def_of_ne_zero hn0, ← Complex.ofReal_natCast n, ← Complex.ofReal_log hnR.le]
  have e1 : cexp (-s * ((Real.log ((N : ℝ) ^ 2) + 2 * Real.log n : ℝ) : ℂ)) =
      cexp (-s * (Real.log ((N : ℝ) ^ 2) : ℂ)) / cexp ((Real.log n : ℂ) * (2 * s)) := by
    rw [eq_div_iff (Complex.exp_ne_zero _), ← Complex.exp_add]; congr 1; push_cast; ring
  rw [e1]
  field_simp

omit [NeZero N] in
theorem summable_totient_series {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun k => (((N ^ 2) * k).totient : ℂ)) (2 * s) := by
  refine LSeriesSummable_of_le_const_mul_rpow (x := 2) (by simp; linarith) ⟨(N : ℝ) ^ 2, fun k hk => ?_⟩
  rw [Complex.norm_natCast, show (2 : ℝ) - 1 = ((1 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, pow_one]
  have := Nat.totient_le (N ^ 2 * k)
  exact_mod_cast this

/-- **The constant term as a Dirichlet series** (`Re s > 1`):
`Σ_c cterm_c(z,s) = 2 · pref(s,z) · Σ_n φ(N²n) n^{-2s}`. -/
theorem tsum_cterm {s : ℂ} (hs : 1 < s.re) (z : ℍ) :
    ∑' c, cterm N s z c = 2 * pref N s z * LSeries (fun k => (((N ^ 2) * k).totient : ℂ)) (2 * s) := by
  have hN : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hinj : Function.Injective (fun c' : ℤ => (N : ℤ) * c') := fun a b h => mul_left_cancel₀ hN h
  have hsupp : Function.support (cterm N s z) ⊆ Set.range (fun c' : ℤ => (N : ℤ) * c') := by
    intro c hc
    by_contra hr
    apply hc
    have hnd : ¬ (N : ℤ) ∣ c := fun ⟨c', hc'⟩ => hr ⟨c', hc'.symm⟩
    unfold cterm
    split_ifs
    · rfl
    · rw [ksum_zero_of_not_dvd N hnd, mul_zero, mul_zero]
  rw [← hinj.tsum_eq hsupp]
  set G : ℤ → ℂ := fun c' => cterm N s z ((N : ℤ) * c')
  have hG : Function.Even G := fun c' => by
    simp only [G]; rw [mul_neg, cterm_neg]
  have hGs : Summable G := (summable_cterm N hs z).comp_injective hinj
  rw [show (∑' c' : ℤ, cterm N s z ((N : ℤ) * c')) = ∑' c', G c' from rfl,
    tsum_int_eq_zero_add_two_mul_tsum_pnat hG hGs]
  have hG0 : G 0 = 0 := by simp [G, cterm]
  rw [hG0, zero_add]
  have hpn : ∀ n : ℕ+, G ((n : ℕ) : ℤ) = pref N s z * LSeries.term (fun k => (((N ^ 2) * k).totient : ℂ)) (2 * s) n :=
    fun n => cterm_nat N s z n.pos
  simp_rw [hpn]
  rw [tsum_mul_left]
  have hL := summable_totient_series N hs
  unfold LSeries
  rw [← tsum_zero_pnat_eq_tsum_nat hL, LSeries.term_zero, zero_add, nsmul_eq_mul]
  push_cast; ring

/-- **The continued constant term** `2 pref(s,z) φ(N²) L(μχ_{N²}, 2s) ζ(2s - 1)`. -/
noncomputable def constTerm (s : ℂ) (z : ℍ) : ℂ :=
  2 * pref N s z * ((Nat.totient (N ^ 2) : ℂ) * (LSeries (muChi (N ^ 2)) (2 * s) * riemannZeta (2 * s - 1)))

theorem tsum_cterm_eq_constTerm {s : ℂ} (hs : 1 < s.re) (z : ℍ) : ∑' c, cterm N s z c = constTerm N s z := by
  rw [tsum_cterm N hs z, constTerm, LSeries_totient_mul (N ^ 2) (pow_pos (Nat.pos_of_ne_zero (NeZero.ne N)) 2) (by simp; linarith)]

open GaloisForLFunctions.RHTower.SelbergPoincare in
/-- **Eisenstein series with continued constant term** (`N ≥ 3`, `Re s > 1`):
`E(z,s) = y^s + constTerm(s,z) + E^*(z,s)`. -/
theorem eisenstein_eq (hN : 3 ≤ N) {s : ℂ} (hs : 1 < s.re) (z : ℍ) :
    poincare N 0 s z = (z.im : ℂ) ^ s + constTerm N s z + Estar N s z := by
  rw [eisenstein_decomp N hN hs z, tsum_cterm_eq_constTerm N hs z]

theorem differentiableAt_LSeries_muChi (M : ℕ) {s : ℂ} (hs : 1 / 2 < s.re) :
    DifferentiableAt ℂ (fun s : ℂ => LSeries (muChi M) (2 * s)) s := by
  have habs : LSeries.abscissaOfAbsConv (muChi M) ≤ (1 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (fun y hy => summable_muChi M (by simpa using hy))
  have hmem : (2 * s) ∈ {w : ℂ | LSeries.abscissaOfAbsConv (muChi M) < (w.re : EReal)} := by
    simp only [Set.mem_setOf_eq]
    refine lt_of_le_of_lt habs ?_
    have : (1 : ℝ) < (2 * s).re := by simp; linarith
    exact_mod_cast this
  have hopen : IsOpen {w : ℂ | LSeries.abscissaOfAbsConv (muChi M) < (w.re : EReal)} :=
    isOpen_lt continuous_const (continuous_coe_real_ereal.comp Complex.continuous_re)
  exact ((LSeries_differentiableOn (muChi M)).differentiableAt (hopen.mem_nhds hmem)).comp s
    ((differentiable_id.const_mul 2) s)

/-- **Meromorphic continuation**: `constTerm(·, z)` is holomorphic on `Re s > 1/2`, `s ≠ 1`. -/
theorem differentiableAt_constTerm (z : ℍ) {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (fun s => constTerm N s z) s := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hpref : DifferentiableAt ℂ (fun s => pref N s z) s := by
    unfold pref
    exact ((((differentiable_exp_neg_mul _).differentiableAt).mul (differentiable_exp_neg_mul _).differentiableAt).mul
      (differentiableAt_fourier_ker le_rfl (div_pos z.im_pos hN) hs 0)).div_const _
  have hz : DifferentiableAt ℂ (fun s : ℂ => riemannZeta (2 * s - 1)) s := by
    refine (differentiableAt_riemannZeta ?_).comp s (((differentiable_id.const_mul 2).sub_const 1) s)
    intro h; apply hs1; linear_combination h / 2
  unfold constTerm
  exact (hpref.const_mul 2).mul ((differentiableAt_LSeries_muChi (N ^ 2) hs).mul hz |>.const_mul _)

end GaloisForLFunctions.RHTower.SelbergEisensteinContinuation
