import GaloisForLFunctions.RHTower.BurnolCoPoissonGeneralSeedMellin
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheZerosSeeEveryAtomicVectorThroughItsMobiusHorizons
import GaloisForLFunctions.BezoutValuationIncidence.RamanujanLagCoefficientAndTotientQuotient

/-!
# The horizon term of a conductor

On the zero side the Ramanujan packet of conductor `e` is read through its Dirichlet polynomial
`D_e(s; N) = Σ_{n≤N} c_e(n) n^{s−1}`. Since `c_e(n) = Σ_{d ∣ (e,n)} μ(e/d) d`, regrouping `n = dk`
gives `D_e(s;N) = Σ_{d∣e} μ(e/d) d^s H(s; ⌊N/d⌋)` with the partial zeta sums
`H(s; M) = Σ_{k≤M} k^{s−1} = ζ(1 − s) + M^s/s + o(1)` on `0 < Re s < 1`. The boundary terms
`μ(e/d) d^s (N/d)^s / s` add up to `(N^s/s) Σ_{d∣e} μ(e/d)`, which vanishes unless `e = 1`.

* **Horizon law** (`tendsto_conductorDirichlet_sub_horizonTerm`): on the open strip,
  `D_e(s;N) − [e = 1] N^s/s → ζ(1 − s) J_s(e)` with the complex Jordan totient
  `J_s(e) = Σ_{d∣e} μ(e/d) d^s`.
* **At a zero** (`tendsto_conductorDirichlet_of_zeta_eq_zero`): if `ζ(1 − s) = 0` the whole
  packet is its horizon term up to `o(1)`; for `e > 1` it tends to `0`.

Only the pole conductor carries a horizon term: a fixed conductor packet meets the zeros at the
horizon only through `e = 1`.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open BezoutValuationIncidence

/-- The conductor Dirichlet polynomial `D_e(s;N) = Σ_{n≤N} c_e(n) n^{s−1}`. -/
def conductorDirichlet (e N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Icc 1 N, (ramanujanLagCoefficient e n : ℂ) * ((n : ℝ) : ℂ) ^ (s - 1)

/-- The complex Jordan totient `J_s(e) = Σ_{d∣e} μ(e/d) d^s`. -/
def jordanC (e : ℕ) (s : ℂ) : ℂ :=
  ∑ d ∈ e.divisors, (moebiusReal (e / d) : ℂ) * ((d : ℝ) : ℂ) ^ s

/-- The horizon term `[e = 1] N^s / s`. -/
def horizonTerm (e N : ℕ) (s : ℂ) : ℂ := if e = 1 then ((N : ℝ) : ℂ) ^ s / s else 0

/-- The partial zeta sum `H(s;M) = Σ_{k≤M} k^{s−1}`. -/
def partialZeta (s : ℂ) (M : ℕ) : ℂ := ∑ k ∈ Icc 1 M, ((k : ℝ) : ℂ) ^ (s - 1)

theorem sum_divisors_moebiusReal (e : ℕ) :
    ∑ d ∈ e.divisors, moebiusReal (e / d) = if e = 1 then 1 else 0 := by
  rw [Nat.sum_div_divisors e fun d => moebiusReal d]
  have h := congrArg (fun f : ArithmeticFunction ℝ => f e)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  simpa only [moebiusReal, ArithmeticFunction.intCoe_apply] using h

/-- `d · (d k)^{s−1} = d^s k^{s−1}`. -/
theorem natCast_mul_cpow_sub_one {d k : ℕ} (hd : 1 ≤ d) (s : ℂ) :
    ((d : ℝ) : ℂ) * (((d * k : ℕ) : ℝ) : ℂ) ^ (s - 1) =
      ((d : ℝ) : ℂ) ^ s * ((k : ℝ) : ℂ) ^ (s - 1) := by
  have hd0 : ((d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  rw [Nat.cast_mul, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg d) (Nat.cast_nonneg k), ← mul_assoc,
    Complex.cpow_sub _ _ hd0, Complex.cpow_one, mul_div_cancel₀ _ hd0]

/-- **Möbius splitting**: `D_e(s;N) = Σ_{d∣e} μ(e/d) d^s H(s; ⌊N/d⌋)`. -/
theorem conductorDirichlet_eq (e N : ℕ) (s : ℂ) :
    conductorDirichlet e N s =
      ∑ d ∈ e.divisors, (moebiusReal (e / d) : ℂ) * ((d : ℝ) : ℂ) ^ s * partialZeta s (N / d) := by
  unfold conductorDirichlet ramanujanLagCoefficient partialZeta
  simp only [Complex.ofReal_sum, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun d hd => ?_
  have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
  have hfil : ∑ n ∈ Icc 1 N, ((moebiusReal (e / d) * if d ∣ n then (d : ℝ) else 0 : ℝ) : ℂ) *
        ((n : ℝ) : ℂ) ^ (s - 1) =
      ∑ n ∈ (Icc 1 N).filter (d ∣ ·), (moebiusReal (e / d) : ℂ) *
        (((d : ℝ) : ℂ) * ((n : ℝ) : ℂ) ^ (s - 1)) := by
    rw [sum_filter]
    refine sum_congr rfl fun n _ => ?_
    split_ifs <;> push_cast <;> ring
  rw [hfil, RenormalizedArithmeticPotentialTheory.sum_Icc_filter_dvd hd1, mul_sum, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [natCast_mul_cpow_sub_one hd1]
  ring

/-- `H(s;M) = ζ(1−s) + M^s/s + E(1−s, M)`. -/
theorem partialZeta_eq (s : ℂ) (M : ℕ) :
    partialZeta s M = riemannZeta (1 - s) + ((M : ℝ) : ℂ) ^ s / s +
      RHTower.zetaStripError (1 - s) M := by
  have h := RHTower.sum_cpow_eq_zetaStripError (1 - s) M
  rw [show -(1 - s) = s - 1 by ring, show (1 : ℂ) - (1 - s) = s by ring] at h
  exact h

/-- The boundary terms add up to the horizon term. -/
theorem horizonTerm_eq_sum (e N : ℕ) (s : ℂ) :
    horizonTerm e N s = ∑ d ∈ e.divisors,
      (moebiusReal (e / d) : ℂ) * ((d : ℝ) : ℂ) ^ s * (((N : ℝ) / d : ℝ) : ℂ) ^ s / s := by
  have hterm : ∀ d ∈ e.divisors, (moebiusReal (e / d) : ℂ) * ((d : ℝ) : ℂ) ^ s *
      (((N : ℝ) / d : ℝ) : ℂ) ^ s / s = (moebiusReal (e / d) : ℂ) * (((N : ℝ) : ℂ) ^ s / s) := by
    intro d hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
    rw [mul_assoc, ← Complex.mul_cpow_ofReal_nonneg hd0.le (div_nonneg (Nat.cast_nonneg N) hd0.le),
      mul_div_cancel₀ _ hd0.ne']
    ring
  rw [sum_congr rfl hterm, ← sum_mul]
  have hμ := congrArg (fun r : ℝ => (r : ℂ)) (sum_divisors_moebiusReal e)
  simp only [Complex.ofReal_sum] at hμ
  rw [hμ, horizonTerm]
  split_ifs <;> simp

/-- A floor inside a complex power is invisible in the limit on `Re s < 1`. -/
theorem tendsto_floor_cpow_sub {s : ℂ} (hs1 : s.re < 1) {d : ℕ} (hd : 1 ≤ d) :
    Tendsto (fun N : ℕ => ((N / d : ℕ) : ℝ) ^ s - (((N : ℝ) / d : ℝ) : ℂ) ^ s) atTop
      (𝓝 0) := by
  have hdiv : Tendsto (fun N : ℕ => N / d) atTop atTop := Nat.tendsto_div_const_atTop (by omega)
  have hpow : Tendsto (fun N : ℕ => 2 * ‖s‖ * ((N / d : ℕ) : ℝ) ^ (s.re - 1)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (show 0 < 1 - s.re by linarith)).comp
      (tendsto_natCast_atTop_atTop.comp hdiv)
    have h' := h.const_mul (2 * ‖s‖)
    rw [mul_zero] at h'
    refine h'.congr fun N => ?_
    simp only [Function.comp_apply, neg_sub]
  refine squeeze_zero_norm' ?_ hpow
  have hev : ∀ᶠ N : ℕ in atTop, ‖s‖ ≤ ((N / d : ℕ) : ℝ) ∧ 1 ≤ N / d :=
    (hdiv.eventually (eventually_ge_atTop ⌈‖s‖⌉₊)).and (hdiv.eventually (eventually_ge_atTop 1))
      |>.mono fun N hN => ⟨(Nat.le_ceil _).trans (by exact_mod_cast hN.1), hN.2⟩
  filter_upwards [hev] with N hN
  have hfl : ⌊(N : ℝ) / d⌋₊ = N / d := Nat.floor_div_eq_div N d
  have hM : (1 : ℝ) ≤ (N : ℝ) / d := by
    rw [le_div_iff₀ (by exact_mod_cast hd), one_mul]
    exact_mod_cast (Nat.le_div_iff_mul_le (by omega)).mp hN.2 |>.trans_eq' (one_mul d).symm
  have h := RHTower.norm_cpow_natFloor_sub_cpow_le (s := s) hM (by rw [hfl]; exact hN.1)
  rw [hfl] at h
  simpa only [Complex.ofReal_natCast] using h

/-- **Horizon law.** On `0 < Re s < 1`, `D_e(s;N) − [e = 1] N^s/s → ζ(1 − s) J_s(e)`. -/
theorem tendsto_conductorDirichlet_sub_horizonTerm {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (e : ℕ) :
    Tendsto (fun N : ℕ => conductorDirichlet e N s - horizonTerm e N s) atTop
      (𝓝 (riemannZeta (1 - s) * jordanC e s)) := by
  have hs0' : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs0; exact lt_irrefl 0 hs0
  have hw0 : 0 < (1 - s).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hw1 : (1 : ℂ) - s ≠ 1 := fun h => hs0' (by linear_combination -h)
  have hrw : ∀ N : ℕ, conductorDirichlet e N s - horizonTerm e N s =
      ∑ d ∈ e.divisors, (moebiusReal (e / d) : ℂ) * ((d : ℝ) : ℂ) ^ s *
        (riemannZeta (1 - s) + (((N / d : ℕ) : ℝ) ^ s - (((N : ℝ) / d : ℝ) : ℂ) ^ s) / s +
          RHTower.zetaStripError (1 - s) (N / d)) := by
    intro N
    rw [conductorDirichlet_eq, horizonTerm_eq_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun d _ => ?_
    rw [partialZeta_eq]
    field_simp
    ring
  simp_rw [hrw]
  rw [jordanC, mul_sum]
  refine tendsto_finset_sum _ fun d hd => ?_
  have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
  have hlim : Tendsto (fun N : ℕ => riemannZeta (1 - s) +
      (((N / d : ℕ) : ℝ) ^ s - (((N : ℝ) / d : ℝ) : ℂ) ^ s) / s +
        RHTower.zetaStripError (1 - s) (N / d)) atTop (𝓝 (riemannZeta (1 - s) + 0 / s + 0)) :=
    ((tendsto_const_nhds.add ((tendsto_floor_cpow_sub hs1 hd1).div_const s)).add
      ((RHTower.tendsto_zetaStripError hw0 hw1).comp (Nat.tendsto_div_const_atTop (by omega))))
  rw [zero_div, add_zero, add_zero] at hlim
  have := hlim.const_mul ((moebiusReal (e / d) : ℂ) * ((d : ℝ) : ℂ) ^ s)
  convert this using 1
  ring

/-- **At a zero.** If `ζ(1 − s) = 0` on the open strip, the conductor Dirichlet polynomial is its
horizon term up to `o(1)`. -/
theorem tendsto_conductorDirichlet_of_zeta_eq_zero {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hz : riemannZeta (1 - s) = 0) (e : ℕ) :
    Tendsto (fun N : ℕ => conductorDirichlet e N s - horizonTerm e N s) atTop (𝓝 0) := by
  simpa only [hz, zero_mul] using tendsto_conductorDirichlet_sub_horizonTerm hs0 hs1 e

/-- Conductors `e ≠ 1` have no horizon term. -/
theorem horizonTerm_of_ne_one {e : ℕ} (he : e ≠ 1) (N : ℕ) (s : ℂ) : horizonTerm e N s = 0 := by
  simp [horizonTerm, he]

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
