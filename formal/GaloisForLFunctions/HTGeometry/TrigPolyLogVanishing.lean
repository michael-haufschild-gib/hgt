import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Trigonometric polynomials cannot vanish along the logarithms of the integers

A finite trigonometric polynomial with integer frequencies,

`T(x) = ∑_{h ∈ S} b_h e^{i λ h x}`,

is continuous and periodic with period `2π/|λ|`.  If it tends to zero along the sequence
`x = log N`, `N → ∞`, then it vanishes identically, and hence every coefficient is zero.

Two mechanisms.  First, for a fixed `x` the integers `⌊e^{x + k p}⌋` reproduce `x` modulo the period
up to an error `≤ 1/⌊e^{x+kp}⌋`, so periodicity plus continuity forces `T(x) = 0` from the
convergence along `log N` alone — no Lipschitz or equidistribution input is needed.  Second,
substituting `w = e^{iλx}` turns `T` into a Laurent polynomial in `w`; it vanishes on infinitely many
points of the unit circle, so it is the zero polynomial and its coefficients are the `b_h`.

This is the endgame of a coefficient-chirp obstruction: a nonzero finite trigonometric polynomial
supplies the contradiction once the differential relation has been reduced to
`T(log N) = O(N^{-η})`.
-/

open Filter Topology Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Periodic functions vanishing along the logarithms of the integers -/

/-- **A periodic continuous function vanishing along `log N` vanishes identically.** -/
theorem eq_zero_of_periodic_of_tendsto_natLog {T : ℝ → ℂ} {p : ℝ} (hp : 0 < p)
    (hper : Function.Periodic T p) (hcont : Continuous T)
    (hlim : Tendsto (fun N : ℕ => T (Real.log N)) atTop (𝓝 0)) (x : ℝ) : T x = 0 := by
  set y : ℕ → ℝ := fun k => x + k * p with hy
  set N : ℕ → ℕ := fun k => ⌊Real.exp (y k)⌋₊ with hN
  -- the sample points go to infinity
  have hytop : Tendsto y atTop atTop := by
    refine Filter.tendsto_atTop_add_const_left atTop x ?_
    exact Filter.Tendsto.atTop_mul_const hp tendsto_natCast_atTop_atTop
  have hexptop : Tendsto (fun k : ℕ => Real.exp (y k)) atTop atTop :=
    Real.tendsto_exp_atTop.comp hytop
  have hNtop : Tendsto N atTop atTop :=
    tendsto_nat_floor_atTop.comp hexptop
  -- eventually the floor is at least one
  have hev : ∀ᶠ k in atTop, 1 ≤ N k := hNtop.eventually_ge_atTop 1
  -- the defect
  set δ : ℕ → ℝ := fun k => y k - Real.log (N k) with hδ
  have hδnonneg : ∀ᶠ k in atTop, 0 ≤ δ k := by
    filter_upwards [hev] with k hk
    have hfloor : ((N k : ℕ) : ℝ) ≤ Real.exp (y k) := Nat.floor_le (Real.exp_pos _).le
    have hpos : (0 : ℝ) < (N k : ℝ) := by exact_mod_cast hk
    have := Real.log_le_log hpos hfloor
    rw [Real.log_exp] at this
    simpa [hδ] using this
  have hδle : ∀ᶠ k in atTop, δ k ≤ 1 / (N k : ℝ) := by
    filter_upwards [hev] with k hk
    have hpos : (0 : ℝ) < (N k : ℝ) := by exact_mod_cast hk
    have hlt : Real.exp (y k) < (N k : ℝ) + 1 := by
      have := Nat.lt_floor_add_one (Real.exp (y k))
      linarith
    have hlog : y k < Real.log ((N k : ℝ) + 1) := by
      have := Real.log_lt_log (Real.exp_pos _) hlt
      rwa [Real.log_exp] at this
    have hsplit : Real.log ((N k : ℝ) + 1) - Real.log (N k : ℝ) ≤ 1 / (N k : ℝ) := by
      rw [← Real.log_div (by positivity) (ne_of_gt hpos)]
      have hle : Real.log (((N k : ℝ) + 1) / (N k : ℝ)) ≤ ((N k : ℝ) + 1) / (N k : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have heq : ((N k : ℝ) + 1) / (N k : ℝ) - 1 = 1 / (N k : ℝ) := by
        field_simp
        ring
      linarith
    simp only [hδ]
    linarith
  -- the defect vanishes
  have hδzero : Tendsto δ atTop (𝓝 0) := by
    have hmaj : Tendsto (fun k : ℕ => 1 / (N k : ℝ)) atTop (𝓝 0) := by
      have hcast : Tendsto (fun k : ℕ => (N k : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.comp hNtop
      exact Tendsto.congr (fun k => by simp [one_div]) hcast.inv_tendsto_atTop
    refine squeeze_zero' hδnonneg hδle hmaj
  -- periodicity moves the sample point back
  have hshift : ∀ k : ℕ, T (Real.log (N k)) = T (x - δ k) := by
    intro k
    have hval : Real.log (N k) = (x - δ k) + k * p := by
      simp only [hδ, hy]
      ring
    rw [hval]
    exact (hper.nat_mul k) (x - δ k)
  -- pass to the limit
  have hcontlim : Tendsto (fun k : ℕ => T (x - δ k)) atTop (𝓝 (T x)) := by
    have hpt : Tendsto (fun k : ℕ => x - δ k) atTop (𝓝 x) := by
      have := (tendsto_const_nhds (x := x) (f := atTop (α := ℕ))).sub hδzero
      simpa using this
    exact (hcont.tendsto x).comp hpt
  have hzero : Tendsto (fun k : ℕ => T (x - δ k)) atTop (𝓝 0) := by
    refine (hlim.comp hNtop).congr fun k => ?_
    exact (hshift k)
  exact tendsto_nhds_unique hcontlim hzero

/-! ## Trigonometric polynomials with integer frequencies -/

/-- A finite trigonometric polynomial with integer frequencies. -/
def trigPoly (S : Finset ℤ) (b : ℤ → ℂ) (lam : ℝ) (x : ℝ) : ℂ :=
  ∑ h ∈ S, b h * Complex.exp (((lam * h * x : ℝ)) * Complex.I)

theorem continuous_trigPoly (S : Finset ℤ) (b : ℤ → ℂ) (lam : ℝ) :
    Continuous (trigPoly S b lam) := by
  unfold trigPoly
  refine continuous_finsetSum _ fun h _ => ?_
  fun_prop

/-- The trigonometric polynomial is periodic with period `2π/|λ|`. -/
theorem periodic_trigPoly {lam : ℝ} (hlam : lam ≠ 0) (S : Finset ℤ) (b : ℤ → ℂ) :
    Function.Periodic (trigPoly S b lam) (2 * Real.pi / |lam|) := by
  intro x
  unfold trigPoly
  refine Finset.sum_congr rfl fun h _ => ?_
  congr 1
  have habs : |lam| ≠ 0 := abs_ne_zero.mpr hlam
  have hsign : lam / |lam| = 1 ∨ lam / |lam| = -1 := by
    rcases lt_or_gt_of_ne hlam with hneg | hpos
    · right
      rw [abs_of_neg hneg]
      field_simp
    · left
      rw [abs_of_pos hpos]
      field_simp
  have hone : Complex.exp ((((h : ℝ) * (lam / |lam|) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I)
      = 1 := by
    rcases hsign with hs | hs <;> rw [hs]
    · rw [Complex.exp_eq_one_iff]
      exact ⟨h, by push_cast; ring⟩
    · rw [Complex.exp_eq_one_iff]
      exact ⟨-h, by push_cast; ring⟩
  have hreal : (lam * (h : ℝ) * (x + 2 * Real.pi / |lam|) : ℝ)
      = (lam * (h : ℝ) * x : ℝ) + ((h : ℝ) * (lam / |lam|) * (2 * Real.pi) : ℝ) := by
    field_simp
  rw [hreal, Complex.ofReal_add, add_mul, Complex.exp_add, hone, mul_one]

/-! ## Linear independence of the characters -/

/-- The unit-circle points `exp(i/(k+1))` are pairwise distinct. -/
theorem injective_exp_inv_succ :
    Function.Injective (fun k : ℕ => Complex.exp (((1 / ((k : ℝ) + 1) : ℝ)) * Complex.I)) := by
  intro k l hkl
  have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  have hl : (0 : ℝ) < 1 / ((l : ℝ) + 1) := by positivity
  have hk1 : 1 / ((k : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  have hl1 : 1 / ((l : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have := Nat.cast_nonneg (α := ℝ) l
    linarith
  rw [Complex.exp_eq_exp_iff_exists_int] at hkl
  obtain ⟨m, hm⟩ := hkl
  set a : ℝ := 1 / ((k : ℝ) + 1) with hadef
  set c : ℝ := 1 / ((l : ℝ) + 1) with hcdef
  have hprod : ((a - c - (m : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I = 0 := by
    push_cast
    linear_combination hm
  have hcast0 : ((a - c - (m : ℝ) * (2 * Real.pi) : ℝ) : ℂ) = 0 := by
    rcases mul_eq_zero.mp hprod with h | h
    · exact h
    · exact absurd h Complex.I_ne_zero
  have him : a = c + (m : ℝ) * (2 * Real.pi) := by
    have := Complex.ofReal_eq_zero.mp hcast0
    linarith
  have hpi : (3 : ℝ) < 2 * Real.pi := by
    have := Real.pi_gt_three
    linarith
  have hm0 : m = 0 := by
    by_contra hne
    have h1 : (1 : ℝ) ≤ |(m : ℝ)| := by
      have : (1 : ℤ) ≤ |m| := Int.one_le_abs (by exact_mod_cast hne)
      exact_mod_cast this
    have habs : |a - c| < 3 := by
      rw [abs_sub_lt_iff]
      constructor <;> linarith
    have hdiff : a - c = (m : ℝ) * (2 * Real.pi) := by linarith
    rw [hdiff, abs_mul] at habs
    have hpiabs : |(2 : ℝ) * Real.pi| = 2 * Real.pi := abs_of_pos (by linarith)
    rw [hpiabs] at habs
    nlinarith
  rw [hm0] at him
  simp only [Int.cast_zero, zero_mul, add_zero] at him
  have heq : ((k : ℝ) + 1) = ((l : ℝ) + 1) := by
    rw [hadef, hcdef] at him
    have hk0 : ((k : ℝ) + 1) ≠ 0 := by positivity
    have hl0 : ((l : ℝ) + 1) ≠ 0 := by positivity
    field_simp at him
    linarith
  have : (k : ℝ) = (l : ℝ) := by linarith
  exact_mod_cast this

/-- **A trigonometric polynomial vanishing identically has vanishing coefficients.** -/
theorem trigPoly_coeff_eq_zero {S : Finset ℤ} {b : ℤ → ℂ} {lam : ℝ} (hlam : lam ≠ 0)
    (hzero : ∀ x : ℝ, trigPoly S b lam x = 0) : ∀ h ∈ S, b h = 0 := by
  classical
  rcases S.eq_empty_or_nonempty with hS | hS
  · intro h hh
    rw [hS] at hh
    simp at hh
  -- shift the frequencies into the nonnegative range
  obtain ⟨h₀, hh₀S, hh₀⟩ := S.exists_min_image id hS
  set m : ℤ := -h₀ with hm
  have hshift : ∀ h ∈ S, 0 ≤ h + m := by
    intro h hh
    have := hh₀ h hh
    simp only [id] at this
    omega
  -- the Laurent polynomial in the circle variable
  set P : Polynomial ℂ := ∑ h ∈ S, Polynomial.C (b h) * Polynomial.X ^ (h + m).toNat with hP
  have hroot : ∀ x : ℝ, P.eval (Complex.exp (((lam * x : ℝ)) * Complex.I)) = 0 := by
    intro x
    set w : ℂ := Complex.exp (((lam * x : ℝ)) * Complex.I) with hw
    have hwpow : ∀ h ∈ S, w ^ (h + m).toNat
        = Complex.exp ((((h : ℝ) + (m : ℝ)) * (lam * x) : ℝ) * Complex.I) := by
      intro h hh
      rw [hw, ← Complex.exp_nat_mul]
      congr 1
      have hz : ((h + m).toNat : ℤ) = h + m := Int.toNat_of_nonneg (hshift h hh)
      have hcastC : (((h + m).toNat : ℕ) : ℂ) = (h : ℂ) + (m : ℂ) := by
        exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) hz
      rw [hcastC]
      push_cast
      ring
    have hexpand : P.eval w = ∑ h ∈ S, b h * w ^ (h + m).toNat := by
      rw [hP]
      simp [Polynomial.eval_finsetSum]
    rw [hexpand, Finset.sum_congr rfl (fun h hh => by rw [hwpow h hh])]
    -- factor out the common shift
    have hfac : ∀ h ∈ S, Complex.exp ((((h : ℝ) + (m : ℝ)) * (lam * x) : ℝ) * Complex.I)
        = Complex.exp ((((m : ℝ)) * (lam * x) : ℝ) * Complex.I)
          * Complex.exp (((lam * h * x : ℝ)) * Complex.I) := by
      intro h hh
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [Finset.sum_congr rfl (fun h hh => by rw [hfac h hh])]
    have hpull : ∑ h ∈ S, b h * (Complex.exp ((((m : ℝ)) * (lam * x) : ℝ) * Complex.I)
          * Complex.exp (((lam * h * x : ℝ)) * Complex.I))
        = Complex.exp ((((m : ℝ)) * (lam * x) : ℝ) * Complex.I) * trigPoly S b lam x := by
      rw [trigPoly, Finset.mul_sum]
      exact Finset.sum_congr rfl fun h _ => by ring
    rw [hpull, hzero x, mul_zero]
  -- infinitely many roots
  have hinf : {z : ℂ | P.IsRoot z}.Infinite := by
    refine Set.infinite_of_injective_forall_mem
      (f := fun k : ℕ => Complex.exp (((1 / ((k : ℝ) + 1) : ℝ)) * Complex.I))
      injective_exp_inv_succ ?_
    intro k
    have := hroot (1 / (lam * ((k : ℝ) + 1)))
    have hval : lam * (1 / (lam * ((k : ℝ) + 1))) = 1 / ((k : ℝ) + 1) := by
      field_simp
    rw [hval] at this
    exact this
  have hPzero : P = 0 := Polynomial.eq_zero_of_infinite_isRoot P hinf
  -- read off the coefficients
  intro h hh
  have hinj : ∀ h₁ ∈ S, ∀ h₂ ∈ S, (h₁ + m).toNat = (h₂ + m).toNat → h₁ = h₂ := by
    intro h₁ hh₁ h₂ hh₂ heq
    have e₁ : ((h₁ + m).toNat : ℤ) = h₁ + m := Int.toNat_of_nonneg (hshift h₁ hh₁)
    have e₂ : ((h₂ + m).toNat : ℤ) = h₂ + m := Int.toNat_of_nonneg (hshift h₂ hh₂)
    omega
  have hcoeff : P.coeff (h + m).toNat = b h := by
    rw [hP, Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single h]
    · simp
    · intro h' hh' hne
      have hne' : (h + m).toNat ≠ (h' + m).toNat := fun hc => hne (hinj h' hh' h hh hc.symm)
      simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne']
    · intro hcon
      exact absurd hh hcon
  rw [← hcoeff, hPzero]
  simp

/-! ## The endgame -/

/-- **A trigonometric polynomial that vanishes along `log N` has vanishing coefficients.** -/
theorem trigPoly_coeff_eq_zero_of_tendsto_natLog {S : Finset ℤ} {b : ℤ → ℂ} {lam : ℝ}
    (hlam : lam ≠ 0)
    (hlim : Tendsto (fun N : ℕ => trigPoly S b lam (Real.log N)) atTop (𝓝 0)) :
    ∀ h ∈ S, b h = 0 := by
  refine trigPoly_coeff_eq_zero hlam ?_
  have hppos : 0 < 2 * Real.pi / |lam| := by
    have := Real.pi_pos
    have : (0 : ℝ) < |lam| := abs_pos.mpr hlam
    positivity
  exact eq_zero_of_periodic_of_tendsto_natLog hppos (periodic_trigPoly hlam S b)
    (continuous_trigPoly S b lam) hlim

end

end GaloisForLFunctions.HTGeometry
