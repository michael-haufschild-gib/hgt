import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheSquareOfACyclotomicRingHasItsContactsOnAProgression
import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheNormalFormOfThePairingOfTheDegreePoints

/-!
# The counterterm of a number ring obeys Riemann–Hurwitz

On a surface `C × C` the form `2 d₁ d₂ − D·D` on a multiple `e Γ` of one Frobenius graph is
`2g e²` in the normalization by the degree. On the comb of the integers the same form on the
degree point `n` is `(2e²/n)(1 + (n/2) log(n/2π))`: the degree point has the **genus**
`g(n) = 1 + (n/2) log(n/2π)` (`genus`, `combForm_singleton`). It is negative at `n = 2, 3` and
positive at every other degree point (`genus_two_neg`, `genus_three_neg`, `genus_one_pos`,
`genus_pos_of_four_le`).

For an abelian number ring, with zeta function `ζ(s) Π_i L(s, χ_i)` over primitive characters
of conductors `q_i`, counted by norms on the comb of the integers:

* **Contacts** (`ringWeight`, `ringWeight_eq`): `Λ(n)(1 + Σ_i Re χ_i(n))`.
* **The pairing** (`ringForm`, `tendsto_ringForm_add_contact`): jets, counterterms and twice the
  contacts tend to `2 d₁ d₂` minus the sum over the zeros of the zeta function of the ring.
* **Riemann–Hurwitz** (`ringForm_eq`, `ringForm_eq_genus`, `riemannHurwitz`): the jets of the
  integers enter `d = 1 + #{χ_i}` times, and the mass at `n` with `d log(n/2π) + R`,
  `R = Σ_i log q_i`. In terms of the genus `g_K(n) = 1 + (n/2)(d log(n/2π) + R)`:
  `2 g_K(n) − 2 = d (2 g(n) − 2) + n R`. The conductors are the ramification term, pulled back
  to the degree point `n` with the multiplicity `n`.
* **The index** (`ringZeroSum_packetCombination`, `tendsto_ringPairing_packetCombination`,
  `negIndex_ringDefect_packets_le`): on combinations of packets the limit is `2 d₁ d₂` minus the
  quadratic form of the sum of the Gram matrices of `ζ` and of the `L(s, χ_i)`; its negative
  squares are at most the zeros of these functions to the right of the line.
* **Short packets** (`tendsto_ringForm_le_degrees_of_short`): when every conductor is at least
  `128π` (or `4π` for an odd character), the inequality holds on packets shorter than `log 2`
  with the margin `∫f²/5000`: the ramification term exceeds the archimedean constant.
-/

open Finset Filter Topology MeasureTheory Matrix
open scoped ComplexConjugate
open Zeta23 GaloisForLFunctions.HTGeometry
open scoped ArithmeticFunction.vonMangoldt Real

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### The genus of a degree point -/

/-- The genus of the degree point `n` on the square of a ring of degree `d` whose conductors
have the product `e^R`: `1 + (n/2)(d log(n/2π) + R)`. For the integers `d = 1`, `R = 0`. -/
def genus (d : ℕ) (R : ℝ) (n : ℕ) : ℝ :=
  1 + (n : ℝ) / 2 * (d * Real.log ((n : ℝ) / (2 * π)) + R)

theorem genus_one_zero (n : ℕ) :
    genus 1 0 n = 1 + (n : ℝ) / 2 * Real.log ((n : ℝ) / (2 * π)) := by
  unfold genus
  push_cast
  ring

/-- **Riemann–Hurwitz for the genus of a degree point.** -/
theorem riemannHurwitz (d : ℕ) (R : ℝ) (n : ℕ) :
    2 * genus d R n - 2 = d * (2 * genus 1 0 n - 2) + n * R := by
  unfold genus
  push_cast
  ring

/-- **The form on one degree point is its genus.** In the normal form of the pairing,
`2 d₁ d₂ − D·D` on the divisor `c·γ_n` is `(2c²/n)·g(n)`. -/
theorem combForm_singleton {n : ℕ} (hn : 0 < n) (c : ℕ → ℝ) :
    HodgeTheoryOfAFixedPart.combForm {n} c = 2 * c n ^ 2 / n * genus 1 0 n := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [genus_one_zero]
  simp only [HodgeTheoryOfAFixedPart.combForm, HodgeTheoryOfAFixedPart.degOne,
    HodgeTheoryOfAFixedPart.degTwo, HodgeTheoryOfAFixedPart.combPairing,
    HodgeTheoryOfAFixedPart.counterterm, Finset.sum_singleton, Finset.erase_singleton,
    Finset.sum_empty, zero_sub]
  field_simp
  ring

theorem exp_two_bounds : (7 : ℝ) < Real.exp 2 ∧ Real.exp 2 < 8 := by
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.exp_one_lt_d9
  have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [h]
  constructor <;> nlinarith [Real.exp_pos 1]

/-- The degree point `2` has negative genus. -/
theorem genus_two_neg : genus 1 0 2 < 0 := by
  rw [genus_one_zero]
  have hπ : Real.exp 1 < π :=
    lt_trans (lt_trans Real.exp_one_lt_d9 (by norm_num)) Real.pi_gt_three
  have h1 : (1 : ℝ) < Real.log π := (Real.lt_log_iff_exp_lt Real.pi_pos).mpr hπ
  have h2 : Real.log (((2 : ℕ) : ℝ) / (2 * π)) = -Real.log π := by
    rw [show ((2 : ℕ) : ℝ) / (2 * π) = π⁻¹ by push_cast; field_simp, Real.log_inv]
  rw [h2]
  push_cast
  linarith

/-- The degree point `3` has negative genus. -/
theorem genus_three_neg : genus 1 0 3 < 0 := by
  rw [genus_one_zero]
  have e23 : Real.exp (2 / 3) < 2 := by
    by_contra hcon
    have hle : (2 : ℝ) ≤ Real.exp (2 / 3) := not_lt.mp hcon
    have h3 : (2 : ℝ) ^ 3 ≤ Real.exp (2 / 3) ^ 3 := pow_le_pow_left₀ (by norm_num) hle 3
    have h4 : Real.exp (2 / 3) ^ 3 = Real.exp 2 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [h4] at h3
    have := exp_two_bounds.2
    norm_num at h3
    linarith
  have hlog : Real.log (((3 : ℕ) : ℝ) / (2 * π)) < -(2 / 3) := by
    rw [Real.log_lt_iff_lt_exp (by positivity), Real.exp_neg]
    have hpi := Real.pi_gt_three
    have h1 : ((3 : ℕ) : ℝ) / (2 * π) < 1 / 2 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      push_cast
      linarith
    have h2 : (1 : ℝ) / 2 < (Real.exp (2 / 3))⁻¹ := by
      rw [one_div, inv_lt_inv₀ (by norm_num) (Real.exp_pos _)]
      exact e23
    linarith
  push_cast at hlog ⊢
  linarith

/-- The degree point `1` has positive genus. -/
theorem genus_one_pos : 0 < genus 1 0 1 := by
  rw [genus_one_zero]
  have hlog : -2 < Real.log (((1 : ℕ) : ℝ) / (2 * π)) := by
    rw [Real.lt_log_iff_exp_lt (by positivity), Real.exp_neg]
    have hpi := Real.pi_lt_d2
    have he := exp_two_bounds.1
    push_cast
    rw [one_div, inv_lt_inv₀ (Real.exp_pos _) (by positivity)]
    linarith
  push_cast at hlog ⊢
  linarith

/-- Every degree point `n ≥ 4` has positive genus. -/
theorem genus_pos_of_four_le {n : ℕ} (hn : 4 ≤ n) : 0 < genus 1 0 n := by
  rw [genus_one_zero]
  have hpi := Real.pi_lt_d2
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  -- `log(n/2π) > −2/n`
  have hlog : -(2 / (n : ℝ)) < Real.log ((n : ℝ) / (2 * π)) := by
    rw [Real.lt_log_iff_exp_lt (by positivity), Real.exp_neg]
    rcases Nat.lt_or_ge n 5 with h5 | h5
    · -- `n = 4`: `exp(1/2) ≥ 13/8`
      have hn : n = 4 := by omega
      subst hn
      have h1 : (13 : ℝ) / 8 ≤ Real.exp (2 / ((4 : ℕ) : ℝ)) := by
        have hq := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 2 / ((4 : ℕ) : ℝ) by positivity)
        have he : (1 : ℝ) + 2 / ((4 : ℕ) : ℝ) + (2 / ((4 : ℕ) : ℝ)) ^ 2 / 2 = 13 / 8 := by
          push_cast
          norm_num
        linarith
      have h2 : (Real.exp (2 / ((4 : ℕ) : ℝ)))⁻¹ ≤ ((13 : ℝ) / 8)⁻¹ := inv_anti₀ (by norm_num) h1
      have h3 : ((13 : ℝ) / 8)⁻¹ < ((4 : ℕ) : ℝ) / (2 * π) := by
        rw [inv_div, div_lt_div_iff₀ (by norm_num) (by positivity)]
        push_cast
        linarith
      linarith
    · -- `n ≥ 5`: `exp(2/n) ≥ 1 + 2/n` and `2π < n + 2`
      have hn5 : (5 : ℝ) ≤ n := by exact_mod_cast h5
      have h1 : 1 + 2 / (n : ℝ) ≤ Real.exp (2 / n) := by
        linarith [Real.add_one_le_exp (2 / (n : ℝ))]
      have h2 : (Real.exp (2 / n))⁻¹ ≤ (1 + 2 / (n : ℝ))⁻¹ := inv_anti₀ (by positivity) h1
      have h3 : (1 + 2 / (n : ℝ))⁻¹ = n / (n + 2) := by
        field_simp
      have h4 : (n : ℝ) / (n + 2) < n / (2 * π) := by
        rw [div_lt_div_iff_of_pos_left hn0 (by positivity) (by positivity)]
        linarith
      linarith
  have key : (n : ℝ) / 2 * (-(2 / (n : ℝ))) < (n : ℝ) / 2 * Real.log ((n : ℝ) / (2 * π)) :=
    mul_lt_mul_of_pos_left hlog (by positivity)
  have hval : (n : ℝ) / 2 * (-(2 / (n : ℝ))) = -1 := by
    field_simp
  linarith

/-! ### The square of a number ring on the comb of the integers -/

section Ring

variable {κ : Type*} [Fintype κ] {q : κ → ℕ} [∀ i, NeZero (q i)] {f : ℝ → ℝ}

/-- The contacts of the ideals of the ring with the characters `χ_i`, counted by their norms. -/
def ringWeight (χ : ∀ i, DirichletCharacter ℂ (q i)) (n : ℕ) : ℝ :=
  Λ n + ∑ i, twistWeight (χ i) n

omit [∀ i, NeZero (q i)] in
theorem ringWeight_eq (χ : ∀ i, DirichletCharacter ℂ (q i)) (n : ℕ) :
    ringWeight χ n = Λ n * (1 + ∑ i, ((χ i) (n : ZMod (q i))).re) := by
  rw [ringWeight, mul_add, mul_one, Finset.mul_sum]
  rfl

omit [∀ i, NeZero (q i)] in
theorem weightedContact_ringWeight (χ : ∀ i, DirichletCharacter ℂ (q i)) (f : ℝ → ℝ)
    (L N : ℕ) :
    weightedContact (ringWeight χ) f L N =
      degreeContact f L N + ∑ i, weightedContact (twistWeight (χ i)) f L N := by
  rw [← weightedContact_vonMangoldt]
  unfold weightedContact
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ringWeight, add_div, add_mul, Finset.sum_div, Finset.sum_mul]

/-- The jets and counterterms of the pairing of the ring: those of the integers and of the
twisted parts of its characters. -/
def ringForm (χ : ∀ i, DirichletCharacter ℂ (q i)) (f : ℝ → ℝ) (L N : ℕ) : ℝ :=
  degreeForm f L N + ∑ i, twistedForm (χ i) f L N

/-- The sum over the zeros of the zeta function of the ring of a packet. -/
def ringZeroSum (hq : ∀ i, 1 < q i) {χ : ∀ i, DirichletCharacter ℂ (q i)}
    (hprim : ∀ i, (χ i).IsPrimitive) (f : ℝ → ℝ) : ℝ :=
  zeroSum f + ∑ i, twistedZeroSum (hq i) (hprim i) f

/-- **The pairing of the square of a number ring is twice the product of the degrees minus the
sum over the zeros of its zeta function.** -/
theorem tendsto_ringForm_add_contact (hq : ∀ i, 1 < q i) {χ : ∀ i, DirichletCharacter ℂ (q i)}
    (hprim : ∀ i, (χ i).IsPrimitive) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {K : ℕ} (hK : 1 ≤ K) (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) :
    Tendsto (fun N : ℕ => ringForm χ f (3 * K) N +
        2 * weightedContact (ringWeight χ) f (3 * K) N) atTop
      (𝓝 (2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) -
        ringZeroSum hq hprim f)) := by
  have h1 := tendsto_degreePairing_degrees_sub_zeroSum hf hfc hK hsupp
  have h2 := tendsto_finsetSum (Finset.univ : Finset κ) fun i _ =>
    tendsto_twistedForm_add_twistedContact (hq i) (hprim i) hf hfc hK hsupp
  have h := h1.add h2
  rw [show 2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) - zeroSum f +
        ∑ i, -twistedZeroSum (hq i) (hprim i) f =
      2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) -
        ringZeroSum hq hprim f by
    rw [ringZeroSum, Finset.sum_neg_distrib]
    ring] at h
  refine h.congr fun N => ?_
  rw [ringForm, weightedContact_ringWeight, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

omit [∀ i, NeZero (q i)] in
/-- **Riemann–Hurwitz for the counterterm.** The jets of the integers enter `d = 1 + #{χ_i}`
times, and the mass with the sum of the logarithms of the conductors besides `d` times the
counterterm of the integers. -/
theorem ringForm_eq (χ : ∀ i, DirichletCharacter ℂ (q i)) (f : ℝ → ℝ) (L N : ℕ) :
    ringForm χ f L N = ((Fintype.card κ : ℝ) + 1) * degreeForm f L N -
      ∑ i, placeJet (χ i) f L N -
      (∑ i, Real.log (q i)) * ∑ n ∈ Ioc N (N + L * N), degreeSample f N n ^ 2 / n := by
  unfold ringForm twistedForm
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Finset.sum_mul]
  ring

omit [∀ i, NeZero (q i)] in
/-- **The mass at a degree point enters with its genus.** With the genus
`g_K(n) = 1 + (n/2)(d log(n/2π) + Σ_i log q_i)` of the degree point on the square of the ring,
the mass at `n` enters the pairing with `(2 g_K(n) − 2)/n`. -/
theorem ringForm_eq_genus (χ : ∀ i, DirichletCharacter ℂ (q i)) (f : ℝ → ℝ) (L N : ℕ) :
    ringForm χ f L N = ((Fintype.card κ : ℝ) + 1) * degreePairing f L N -
      ∑ i, placeJet (χ i) f L N -
      ∑ n ∈ Ioc N (N + L * N), degreeSample f N n ^ 2 / n *
        ((2 * genus (Fintype.card κ + 1) (∑ i, Real.log (q i)) n - 2) / n) := by
  have hterm : ∀ n ∈ Ioc N (N + L * N), degreeSample f N n ^ 2 / n *
      ((2 * genus (Fintype.card κ + 1) (∑ i, Real.log (q i)) n - 2) / n) =
      ((Fintype.card κ : ℝ) + 1) *
          (degreeSample f N n ^ 2 / n * Real.log ((n : ℝ) / (2 * Real.pi))) +
        (∑ i, Real.log (q i)) * (degreeSample f N n ^ 2 / n) := by
    intro n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by
      have := (Finset.mem_Ioc.mp hn).1
      omega)
    unfold genus
    push_cast
    field_simp
    ring
  rw [ringForm_eq, degreeForm, Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-! ### The index -/

section Index

variable {ι : Type*} [Fintype ι]

/-- The sum over the zeros of the zeta function of the ring on a combination of packets is the
quadratic form of the sum of the Gram matrices of the zeros. -/
theorem ringZeroSum_packetCombination (hq : ∀ i, 1 < q i)
    {χ : ∀ i, DirichletCharacter ℂ (q i)} (hprim : ∀ i, (χ i).IsPrimitive) {g : ι → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hgc : ∀ i, HasCompactSupport (g i)) (x : ι → ℝ) :
    ringZeroSum hq hprim (packetCombination g x) =
      hermQuad (ArithmeticCastelnuovoSeveri.zeroGram zetaZeroConfig
          (fun i u => ((g i u : ℝ) : ℂ)) +
        ∑ k, ArithmeticCastelnuovoSeveri.zeroGram
          (_root_.RHTower.dirichletZeros (hq k) (hprim k)) fun i u => ((g i u : ℝ) : ℂ))
        (fun i => ((x i : ℝ) : ℂ)) := by
  classical
  rw [ringZeroSum, hermQuad_add, hermQuad_sum, zeroSum_packetCombination hg hgc x,
    ArithmeticCastelnuovoSeveri.weilGram_eq_zeroGram _
      (fun i => contDiff_ofReal_packet (hg i)) fun i => hasCompactSupport_ofReal_packet (hgc i)]
  congr 1
  exact Finset.sum_congr rfl fun k _ =>
    twistedZeroSum_packetCombination (hq k) (hprim k) hg hgc x

/-- **The pairing of the square of a number ring on a combination of packets**: twice the
product of the degrees minus the quadratic form of the Gram matrices of the zeros of its zeta
function. -/
theorem tendsto_ringPairing_packetCombination (hq : ∀ i, 1 < q i)
    {χ : ∀ i, DirichletCharacter ℂ (q i)} (hprim : ∀ i, (χ i).IsPrimitive) {g : ι → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hgc : ∀ i, HasCompactSupport (g i)) {K : ℕ} (hK : 1 ≤ K)
    (hsupp : ∀ i u, u ≤ Real.log 3 ∨ Real.log K ≤ u → g i u = 0) (x : ι → ℝ) :
    Tendsto (fun N : ℕ => ringForm χ (packetCombination g x) (3 * K) N +
        2 * weightedContact (ringWeight χ) (packetCombination g x) (3 * K) N) atTop
      (𝓝 (2 * ((∫ u, packetCombination g x u * Real.exp (-u / 2)) *
            ∫ u, packetCombination g x u * Real.exp (u / 2)) -
          hermQuad (ArithmeticCastelnuovoSeveri.zeroGram zetaZeroConfig
              (fun i u => ((g i u : ℝ) : ℂ)) +
            ∑ k, ArithmeticCastelnuovoSeveri.zeroGram
              (_root_.RHTower.dirichletZeros (hq k) (hprim k)) fun i u => ((g i u : ℝ) : ℂ))
            (fun i => ((x i : ℝ) : ℂ)))) := by
  have hs : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → packetCombination g x u = 0 := fun u hu =>
    Finset.sum_eq_zero fun i _ => by rw [hsupp i u hu, mul_zero]
  have h := tendsto_ringForm_add_contact hq hprim (contDiff_packetCombination hg x)
    (hasCompactSupport_packetCombination hgc x) hK hs
  rwa [ringZeroSum_packetCombination hq hprim hg hgc x] at h

/-- **The index law on the square of a number ring.** On every finite family of packets the
defect of the pairing has at most as many negative squares as `ζ` and the `L(s, χ_i)` together
have zeros to the right of the critical line. -/
theorem negIndex_ringDefect_packets_le (hq : ∀ i, 1 < q i)
    {χ : ∀ i, DirichletCharacter ℂ (q i)} (hprim : ∀ i, (χ i).IsPrimitive) {g : ι → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hgc : ∀ i, HasCompactSupport (g i)) :
    (hermNegIndex (ArithmeticCastelnuovoSeveri.zeroGram zetaZeroConfig
          (fun i u => ((g i u : ℝ) : ℂ)) +
        ∑ k, ArithmeticCastelnuovoSeveri.zeroGram
          (_root_.RHTower.dirichletZeros (hq k) (hprim k)) fun i u => ((g i u : ℝ) : ℂ)) :
        ℕ∞) ≤
      (ArithmeticCastelnuovoSeveri.rightZeros zetaZeroConfig).encard +
        ∑ k, (ArithmeticCastelnuovoSeveri.rightZeros
          (_root_.RHTower.dirichletZeros (hq k) (hprim k))).encard := by
  classical
  have hZ : ∀ o : Option κ, SquareRootThreshold.TemperedConfig (o.elim zetaZeroConfig fun k =>
      _root_.RHTower.dirichletZeros (hq k) (hprim k)) := by
    intro o
    cases o with
    | none => exact SquareRootThreshold.temperedConfig_zetaZeroConfig
    | some k => exact temperedConfig_dirichletZeros (hq k) (hprim k)
  have h := negIndex_sum_zeroGram_le
    (fun o : Option κ => o.elim zetaZeroConfig fun k =>
      _root_.RHTower.dirichletZeros (hq k) (hprim k))
    hZ (fun i u => ((g i u : ℝ) : ℂ)) (fun i => contDiff_ofReal_packet (hg i))
    fun i => hasCompactSupport_ofReal_packet (hgc i)
  rw [Fintype.sum_option, Fintype.sum_option] at h
  exact h

end Index

/-! ### Short packets -/

/-- **The inequality on the square of a number ring where no contact enters.** When every
character is odd of conductor at least `4π` or even of conductor at least `128π`, the pairing
of a packet shorter than `log 2` has a limit, at most twice the product of the degrees minus
`∫ f²/5000`. -/
theorem tendsto_ringForm_le_degrees_of_short (hq : ∀ i, 1 < q i)
    {χ : ∀ i, DirichletCharacter ℂ (q i)} (hprim : ∀ i, (χ i).IsPrimitive)
    (hlarge : ∀ i, ((χ i).Odd ∧ 4 * π ≤ q i) ∨ ((χ i).Even ∧ 128 * π ≤ q i))
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {K : ℕ} (hK : 1 ≤ K)
    (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) {c a : ℝ} (ha0 : 0 ≤ a)
    (ha : 2 * a < Real.log 2) (hshort : ∀ u, a < |u - c| → f u = 0) :
    ∃ l : ℝ, Tendsto (fun N : ℕ => ringForm χ f (3 * K) N +
          2 * weightedContact (ringWeight χ) f (3 * K) N) atTop (𝓝 l) ∧
      l ≤ 2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) -
        1 / 5000 * ∫ u, f u ^ 2 := by
  refine ⟨_, tendsto_ringForm_add_contact hq hprim hf hfc hK hsupp, ?_⟩
  have h1 := zeroSum_ge_of_width hf hfc (c := c) fun u hu => hshort u (by
    have := Real.log_two_lt_d9
    linarith)
  have h2 : 0 ≤ ∑ i, twistedZeroSum (hq i) (hprim i) f :=
    Finset.sum_nonneg fun i _ =>
      twistedZeroSum_nonneg_of_short (hq i) (hprim i) (hlarge i) hf hfc ha0 ha hshort
  rw [ringZeroSum]
  linarith

end Ring

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
