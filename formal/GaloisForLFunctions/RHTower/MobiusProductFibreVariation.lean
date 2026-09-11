import GaloisForLFunctions.RHTower.MobiusLaplaceGammaHankelWall
import GaloisForLFunctions.RHTower.SquarefreeLowerDensity
import Mathlib.NumberTheory.ArithmeticFunction.Liouville

/-!
# Literal Möbius product fibres and their variation

Every nonzero Möbius pair with product `q` has the Liouville sign of `q`,
including pairs with common prime factors. The original finite Gamma--Hankel
energy is therefore exactly a Liouville-weighted sum of nonnegative product
fibres. Square-product fibres give precisely the diagonal energy; nonsquare
products give precisely the signed off-diagonal covariance.

The elementary squarefree density bound forces total absolute fibre variation
to grow at least as `(2 ^ (-r) / 16) * N ^ (2 - r)`. After the uniformly bounded
diagonal is removed, nonsquare absolute variation still tends to infinity for
`1 < r < 2`. These are classification and variation theorems, not an upper
bound or a divergence statement for the signed covariance.
-/

open Filter Topology Finset
open scoped BigOperators
noncomputable section
namespace RHTower.MobiusProductFibre

/-- The real Möbius coefficient at the original integer index. -/
def mu (n : ℕ) : ℝ := (ArithmeticFunction.moebius n : ℤ)
/-- The real Liouville sign of an integer product. -/
def sign (n : ℕ) : ℝ := (ArithmeticFunction.liouville n : ℤ)
/-- All ordered pairs in the original common integer cutoff. -/
def pairs (N : ℕ) : Finset (ℕ × ℕ) := (Icc 1 N) ×ˢ (Icc 1 N)
/-- The squarefree pair weight before its arithmetic sign is applied. -/
def unsignedTerm (r : ℝ) (p : ℕ × ℕ) : ℝ :=
  mu p.1 ^ 2 * mu p.2 ^ 2 / ((p.1+p.2 : ℕ) : ℝ)^r
/-- The original signed Gamma--Hankel summand without the Gamma factor. -/
def signedTerm (r : ℝ) (p : ℕ × ℕ) : ℝ :=
  mu p.1 * mu p.2 / ((p.1+p.2 : ℕ) : ℝ)^r
/-- The complete nonnegative weight at one integer product. -/
def unsignedFibre (N q : ℕ) (r : ℝ) : ℝ :=
  ∑ p ∈ (pairs N).filter (fun p => p.1*p.2=q), unsignedTerm r p
/-- The complete signed weight at one integer product. -/
def signedFibre (N q : ℕ) (r : ℝ) : ℝ :=
  ∑ p ∈ (pairs N).filter (fun p => p.1*p.2=q), signedTerm r p
/-- Total variation after grouping by exact integer product. -/
def variation (N : ℕ) (r : ℝ) : ℝ :=
  ∑ q ∈ Icc 1 (N^2), |signedFibre N q r|

private theorem mu_sq (n : ℕ) : mu n ^ 2 = if Squarefree n then 1 else 0 := by
  by_cases hn : Squarefree n
  · rw [if_pos hn, mu, ArithmeticFunction.moebius_apply_of_squarefree hn]
    push_cast
    rw [pow_two, ← mul_pow]
    norm_num
  · simp [mu, hn, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn]

private theorem mu_eq_sign_mul_sq (n : ℕ) : mu n = sign n * mu n ^ 2 := by
  by_cases hn : Squarefree n
  · rw [mu_sq, if_pos hn, mul_one]
    simp only [mu, sign, ArithmeticFunction.moebius_apply_of_squarefree hn,
      ArithmeticFunction.liouville_apply hn.ne_zero]
  · simp [mu, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn]

private theorem sign_mul (m n : ℕ) : sign (m*n)=sign m*sign n := by
  simp [sign, ArithmeticFunction.liouville_apply_mul]

/-- The product alone determines the sign of every nonzero Möbius pair. -/
theorem pair_sign (m n : ℕ) :
    mu m * mu n = sign (m*n)*(mu m^2*mu n^2) := by
  calc
    mu m*mu n = (sign m*mu m^2)*(sign n*mu n^2) :=
      congrArg₂ (· * ·) (mu_eq_sign_mul_sq m) (mu_eq_sign_mul_sq n)
    _ = _ := by rw [sign_mul]; ring

private theorem abs_sign {q : ℕ} (hq : q ≠ 0) : |sign q|=1 := by
  simp [sign, ArithmeticFunction.liouville_apply hq]

private theorem unsignedTerm_nonneg (r : ℝ) (p : ℕ × ℕ) : 0 ≤ unsignedTerm r p := by
  unfold unsignedTerm
  positivity

/-- Each unsigned product fibre is nonnegative at every real exponent. -/
theorem unsignedFibre_nonneg (N q : ℕ) (r : ℝ) : 0 ≤ unsignedFibre N q r :=
  sum_nonneg fun p _ => unsignedTerm_nonneg r p

/-- There is no cancellation inside a fixed product fibre. -/
theorem signedFibre_eq_sign_mul_unsigned (N q : ℕ) (r : ℝ) :
    signedFibre N q r = sign q * unsignedFibre N q r := by
  rw [signedFibre, unsignedFibre, mul_sum]
  apply sum_congr rfl
  intro p hp
  have he := (mem_filter.mp hp).2
  simp only [signedTerm, unsignedTerm]
  rw [pair_sign, he]
  ring

/-- Taking the absolute value of a complete fibre retains its full unsigned mass. -/
theorem abs_signedFibre_eq_unsigned (N q : ℕ) (r : ℝ) :
    |signedFibre N q r| = unsignedFibre N q r := by
  by_cases hq : q=0
  · subst q
    have he : (pairs N).filter (fun p => p.1*p.2=0) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro p hp hz
      have hp := mem_product.mp hp
      have h1 := (mem_Icc.mp hp.1).1
      have h2 := (mem_Icc.mp hp.2).1
      rcases Nat.mul_eq_zero.mp hz with hz | hz <;> omega
    rw [signedFibre, unsignedFibre, he]
    simp
  · rw [signedFibre_eq_sign_mul_unsigned, abs_mul, abs_sign hq, one_mul,
      abs_of_nonneg (unsignedFibre_nonneg N q r)]

private theorem product_mem {N : ℕ} {p : ℕ × ℕ} (hp : p ∈ pairs N) :
    p.1*p.2 ∈ Icc 1 (N^2) := by
  obtain ⟨h1,h2⟩ := mem_product.mp hp
  obtain ⟨ha,hb⟩ := mem_Icc.mp h1
  obtain ⟨hc,hd⟩ := mem_Icc.mp h2
  exact mem_Icc.mpr ⟨by nlinarith, by nlinarith [Nat.mul_le_mul hb hd]⟩

/-- Product grouping preserves the complete unsigned pair sum. -/
theorem variation_eq_unsigned_pair_sum (N : ℕ) (r : ℝ) :
    variation N r = ∑ p ∈ pairs N, unsignedTerm r p := by
  simp only [variation, abs_signedFibre_eq_unsigned, unsignedFibre]
  exact sum_fiberwise_of_maps_to (fun p hp => product_mem hp) (unsignedTerm r)

private theorem sum_Icc_eq_shifted_range (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, f n) = ∑ n ∈ range N, f (n+1) := by
  symm
  apply sum_bij (fun n _ => n+1)
  · intro n hn
    simp only [mem_range] at hn
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  · intro a ha b hb he
    omega
  · intro b hb
    have hb := mem_Icc.mp hb
    exact ⟨b-1, mem_range.mpr (by omega), by omega⟩
  · intro n hn
    rfl

/-- Exact product regrouping of the original finite Gamma--Hankel energy. -/
theorem energy_eq_signed_fibres (N : ℕ) (r : ℝ) :
    finiteMobiusGammaHankelEnergy N r =
      Real.Gamma r * ∑ q ∈ Icc 1 (N^2), signedFibre N q r := by
  have hf : (∑ q ∈ Icc 1 (N^2), signedFibre N q r) =
      ∑ p ∈ pairs N, signedTerm r p :=
    sum_fiberwise_of_maps_to (fun p hp => product_mem hp) (signedTerm r)
  rw [hf, finiteMobiusGammaHankelEnergy, finiteGammaHankelEnergy, pairs, sum_product]
  congr 1
  rw [sum_Icc_eq_shifted_range]
  apply sum_congr rfl
  intro m hm
  rw [sum_Icc_eq_shifted_range]
  apply sum_congr rfl
  intro n hn
  simp only [signedTerm, mu, shiftedMobiusRealCoefficient, Nat.add_assoc]
  congr 3
  omega

/-- The physical energy retains the Liouville sign of each complete product fibre. -/
theorem energy_eq_liouville_weighted_fibres (N : ℕ) (r : ℝ) :
    finiteMobiusGammaHankelEnergy N r =
      Real.Gamma r * ∑ q ∈ Icc 1 (N^2), sign q * unsignedFibre N q r := by
  simp only [energy_eq_signed_fibres, signedFibre_eq_sign_mul_unsigned]

private theorem squarefree_mass_lower (N : ℕ) :
    (N:ℝ)/4 ≤ ∑ n ∈ Icc 1 N, mu n ^ 2 := by
  have he : (∑ n ∈ Icc 1 N, mu n ^ 2) =
      (((Icc 1 N).filter (fun n => Squarefree n)).card : ℝ) := by
    simp only [mu_sq]
    simp
  rw [he]
  exact quarter_le_card_squarefree N

/-- Squarefree lower density gives a lower bound for the full absolute variation. -/
theorem variation_lower (N : ℕ) (hN : 1 ≤ N) {r : ℝ} (hr : 0 ≤ r) :
    ((N:ℝ)/4)^2 / (2*(N:ℝ))^r ≤ variation N r := by
  have hpN : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hterm (p : ℕ × ℕ) (hp : p ∈ pairs N) :
      (mu p.1^2*mu p.2^2) / (2*(N:ℝ))^r ≤ unsignedTerm r p := by
    obtain ⟨h1,h2⟩ := mem_product.mp hp
    obtain ⟨ha,hb⟩ := mem_Icc.mp h1
    obtain ⟨hc,hd⟩ := mem_Icc.mp h2
    have hpos : (0:ℝ)<((p.1+p.2:ℕ):ℝ) := by exact_mod_cast (by omega : 0<p.1+p.2)
    have hle : ((p.1+p.2:ℕ):ℝ) ≤ 2*(N:ℝ) := by
      have he : p.1+p.2 ≤ 2*N := by omega
      exact_mod_cast he
    exact div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Real.rpow_pos_of_pos hpos r) (Real.rpow_le_rpow hpos.le hle hr)
  have he : (∑ p ∈ pairs N, (mu p.1^2*mu p.2^2) / (2*(N:ℝ))^r) =
      (∑ n ∈ Icc 1 N, mu n^2)^2 / (2*(N:ℝ))^r := by
    rw [← sum_div, pairs, sum_product, pow_two, sum_mul]
    congr 1
    apply sum_congr rfl
    intro m hm
    rw [mul_sum]
  have hm := squarefree_mass_lower N
  calc
    ((N:ℝ)/4)^2 / (2*(N:ℝ))^r ≤
        (∑ n ∈ Icc 1 N, mu n^2)^2 / (2*(N:ℝ))^r := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [sum_nonneg (fun n (_ : n ∈ Icc 1 N) => sq_nonneg (mu n))]
    _ ≤ variation N r := by rw [← he, variation_eq_unsigned_pair_sum]; exact sum_le_sum hterm

/-- The explicit power lower bound holds at every positive integer cutoff. -/
theorem variation_power_lower (N : ℕ) (hN : 1 ≤ N) {r : ℝ} (hr : 0 ≤ r) :
    (2^(-r)/16) * (N:ℝ)^(2-r) ≤ variation N r := by
  have hpN : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have he : ((N:ℝ)/4)^2 / (2*(N:ℝ))^r = (2^(-r)/16) * (N:ℝ)^(2-r) := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hpN.le,
      Real.rpow_sub hpN, Real.rpow_two, Real.rpow_neg (by norm_num : (0:ℝ)≤2)]
    ring
  rw [← he]
  exact variation_lower N hN hr

/-- Absolute product-fibre variation diverges for every nonnegative exponent below two. -/
theorem tendsto_variation_atTop {r : ℝ} (hr : 0 ≤ r) (hr2 : r < 2) :
    Tendsto (fun N : ℕ => variation N r) atTop atTop := by
  have hc : (0:ℝ)<2^(-r)/16 := by positivity
  have ht : Tendsto (fun N : ℕ => (2^(-r)/16)*(N:ℝ)^(2-r)) atTop atTop :=
    (_root_.tendsto_rpow_atTop (by linarith : 0<2-r)).comp tendsto_natCast_atTop_atTop
      |>.const_mul_atTop hc
  exact tendsto_atTop_mono' atTop
    (eventually_atTop.mpr ⟨1,fun N hN => variation_power_lower N hN hr⟩) ht

/-- For squarefree factors, a square product is exactly a diagonal pair. -/
theorem squarefree_pair_isSquare_iff {m n : ℕ} (hm : Squarefree m) (hn : Squarefree n) :
    IsSquare (m*n) ↔ m=n := by
  constructor
  · rintro ⟨k,hk⟩
    have he : m*n=k^2 := by simpa [pow_two] using hk
    have hmk : m ∣ k := (hm.dvd_pow_iff_dvd (by omega : 2 ≠ 0)).mp ⟨n,he.symm⟩
    have hnk : n ∣ k := (hn.dvd_pow_iff_dvd (by omega : 2 ≠ 0)).mp ⟨m,by nlinarith [he]⟩
    have hm0 : 0 < m := Nat.pos_of_ne_zero hm.ne_zero
    have hn0 : 0 < n := Nat.pos_of_ne_zero hn.ne_zero
    have hk0 : 0 < k := by nlinarith [Nat.mul_pos hm0 hn0]
    have hmle := Nat.le_of_dvd hk0 hmk
    have hnle := Nat.le_of_dvd hk0 hnk
    have hme : m=k := by nlinarith [Nat.mul_le_mul_left m hnle]
    have hne : n=k := by nlinarith [Nat.mul_le_mul_right n hmle]
    exact hme.trans hne.symm
  · rintro rfl
    exact ⟨m,rfl⟩

private theorem weighted_fibres (N : ℕ) (r : ℝ) (w : ℕ → ℝ) :
    (∑ q ∈ Icc 1 (N^2), w q * unsignedFibre N q r) =
      ∑ p ∈ pairs N, w (p.1*p.2)*unsignedTerm r p := by
  calc
    _ = ∑ q ∈ Icc 1 (N^2),
        ∑ p ∈ (pairs N).filter (fun p => p.1*p.2=q),
          w (p.1*p.2)*unsignedTerm r p := by
      simp only [unsignedFibre, mul_sum]
      apply sum_congr rfl
      intro q hq
      apply sum_congr rfl
      intro p hp
      rw [(mem_filter.mp hp).2]
    _ = _ := sum_fiberwise_of_maps_to (fun p hp => product_mem hp) _

private theorem square_selector (r : ℝ) (p : ℕ × ℕ) :
    (if IsSquare (p.1*p.2) then (1:ℝ) else 0)*unsignedTerm r p =
      if p.1=p.2 then unsignedTerm r p else 0 := by
  by_cases h1 : Squarefree p.1
  · by_cases h2 : Squarefree p.2
    · simp only [squarefree_pair_isSquare_iff h1 h2]
      split_ifs <;> simp
    · have hz : unsignedTerm r p=0 := by
        simp [unsignedTerm,mu,ArithmeticFunction.moebius_eq_zero_of_not_squarefree h2]
      simp [hz]
  · have hz : unsignedTerm r p=0 := by
      simp [unsignedTerm,mu,ArithmeticFunction.moebius_eq_zero_of_not_squarefree h1]
    simp [hz]

/-- Square-product fibres recover exactly the physical diagonal energy. -/
theorem diagonal_eq_square_fibres (N : ℕ) (r : ℝ) :
    finiteMobiusGammaHankelDiagonalEnergy N r =
      Real.Gamma r * ∑ q ∈ Icc 1 (N^2),
        (if IsSquare q then (1:ℝ) else 0)*unsignedFibre N q r := by
  rw [weighted_fibres]
  simp_rw [square_selector]
  rw [pairs,sum_product]
  have he : (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
      if m=n then unsignedTerm r (m,n) else 0) =
      ∑ m ∈ Icc 1 N, mu m^2/((2*m:ℕ):ℝ)^r := by
    apply sum_congr rfl
    intro m hm
    have hs : (∑ n ∈ Icc 1 N, if m=n then unsignedTerm r (m,n) else 0) =
        unsignedTerm r (m,m) := by simp [hm]
    rw [hs,unsignedTerm]
    have hm2 : mu m^2*mu m^2=mu m^2 := by rw [mu_sq]; split_ifs <;> norm_num
    simp only [hm2]
    congr 3
    omega
  rw [he,sum_Icc_eq_shifted_range,finiteMobiusGammaHankelDiagonalEnergy]
  rfl

private theorem sign_of_isSquare {q : ℕ} (hq : q ≠ 0) (hs : IsSquare q) : sign q=1 := by
  obtain ⟨m,rfl⟩ := hs
  have hm : m ≠ 0 := by intro hm; simp [hm] at hq
  rw [sign_mul]
  calc
    sign m*sign m = |sign m|^2 := by rw [sq_abs]; ring
    _ = 1 := by rw [abs_sign hm]; norm_num

/-- Nonsquare-product fibres recover exactly the physical signed covariance. -/
theorem covariance_eq_nonsquare_fibres (N : ℕ) (r : ℝ) :
    finiteMobiusGammaHankelOffDiagonalCovariance N r =
      Real.Gamma r * ∑ q ∈ Icc 1 (N^2),
        if IsSquare q then 0 else sign q * unsignedFibre N q r := by
  rw [finiteMobiusGammaHankelOffDiagonalCovariance, energy_eq_liouville_weighted_fibres,
    diagonal_eq_square_fibres, ← mul_sub, ← sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro q hq
  by_cases hs : IsSquare q
  · rw [if_pos hs, if_pos hs,
      sign_of_isSquare (by have := (mem_Icc.mp hq).1; omega) hs]
    ring
  · simp [hs]

/-- Total variation over nonsquare products, with the entire diagonal removed. -/
def crossVariation (N : ℕ) (r : ℝ) : ℝ :=
  ∑ q ∈ Icc 1 (N^2), if IsSquare q then 0 else |signedFibre N q r|

/-- The complete variation splits into diagonal mass and nonsquare variation. -/
theorem variation_eq_square_add_cross (N : ℕ) (r : ℝ) :
    variation N r =
      (∑ q ∈ Icc 1 (N^2), (if IsSquare q then (1:ℝ) else 0)*unsignedFibre N q r) +
        crossVariation N r := by
  rw [variation,crossVariation,← sum_add_distrib]
  apply sum_congr rfl
  intro q hq
  split_ifs <;> simp [abs_signedFibre_eq_unsigned]

/-- The physical diagonal is precisely the square-product part of Gamma-weighted variation. -/
theorem gamma_mul_variation_eq_diagonal_add_cross (N : ℕ) (r : ℝ) :
    Real.Gamma r * variation N r =
      finiteMobiusGammaHankelDiagonalEnergy N r + Real.Gamma r * crossVariation N r := by
  rw [variation_eq_square_add_cross,mul_add,← diagonal_eq_square_fibres]

/-- Removing the bounded diagonal still leaves divergent absolute variation for `1 < r < 2`. -/
theorem tendsto_crossVariation_atTop {r : ℝ} (hr : 1 < r) (hr2 : r < 2) :
    Tendsto (fun N : ℕ => crossVariation N r) atTop atTop := by
  let B : ℝ := ∑' n, mobiusGammaHankelDiagonalMajorant r n
  have hg : 0 < Real.Gamma r := Real.Gamma_pos_of_pos (by linarith)
  have hdiv : Real.Gamma r*(B/Real.Gamma r)=B := by field_simp
  have hlower (N : ℕ) : variation N r-B/Real.Gamma r ≤ crossVariation N r := by
    apply (mul_le_mul_iff_right₀ hg).mp
    rw [mul_sub,hdiv]
    have he := gamma_mul_variation_eq_diagonal_add_cross N r
    have hb : finiteMobiusGammaHankelDiagonalEnergy N r ≤ B :=
      finiteMobiusGammaHankelDiagonalEnergy_le_tsum N hr
    linarith
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [(tendsto_variation_atTop (by linarith : 0 ≤ r) hr2).eventually
    (eventually_ge_atTop (b+B/Real.Gamma r))] with N hN
  linarith [hlower N]

end RHTower.MobiusProductFibre
