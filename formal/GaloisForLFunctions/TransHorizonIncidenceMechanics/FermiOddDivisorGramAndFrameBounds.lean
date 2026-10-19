import Mathlib.NumberTheory.ZetaValues
import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiGcdGramPrimeProductBounds
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Odd-divisor homogeneous Gram identities and prime-product frame bounds

Normalized odd-divisor profiles have a common positive squared norm. Their
literal reciprocal-square inner products equal that norm times the arithmetic
GCD kernel. Every finite packet has a summable squared profile and an exact
finite Gram expansion, giving the classical prime-product frame bounds in the
odd coordinates used by the Fermi ray analysis.

The infinite reindexing is an injective affine map onto the odd multiples.
All finite/infinite sum exchanges use proved summability. These are supporting
ingredients of the antichain classification; no independent contribution is
claimed for the classical GCD or reciprocal-square formulas.
-/

open scoped BigOperators
noncomputable section
namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

private theorem summable_odd_inv_sq :
    Summable (fun m : ℕ => 1 / (((2*m+1 : ℕ) : ℝ)^2)) := by
  exact hasSum_zeta_two.summable.comp_injective
    (show Function.Injective (fun m : ℕ => 2*m+1) by intro a b h; dsimp only at h; omega)

/-- Exact reciprocal-square mass of positive odd multiples of an odd divisor. -/
private theorem tsum_oddMultiples_inv_sq {d : ℕ} (hd : Odd d) :
    (∑' m : ℕ, if d ∣ 2*m+1 then 1 / (((2*m+1 : ℕ) : ℝ)^2) else 0) =
      (∑' m : ℕ, 1 / (((2*m+1 : ℕ) : ℝ)^2)) / (d : ℝ)^2 := by
  obtain ⟨h, hh⟩ := hd
  have hdpos : 0 < d := by omega
  let f : ℕ → ℕ := fun k => d*k+h
  let g : ℕ → ℝ := fun m => if d ∣ 2*m+1 then 1 / (((2*m+1 : ℕ) : ℝ)^2) else 0
  have hinj : Function.Injective f := by
    intro a b hab
    exact mul_left_cancel₀ hdpos.ne' (Nat.add_right_cancel hab)
  have hindex (k : ℕ) : 2*f k+1 = d*(2*k+1) := by
    dsimp [f]
    nlinarith [hh]
  have hsupp : Function.support g ⊆ Set.range f := by
    intro m hm
    have hdiv : d ∣ 2*m+1 := by
      by_contra hn
      simp [g, hn, Function.mem_support] at hm
    obtain ⟨q,hq⟩ := hdiv
    have hdmod : d % 2 = 1 := by omega
    have hqmod : q % 2 = 1 := by
      have hm := congrArg (fun n : ℕ => n % 2) hq
      simpa [Nat.add_mod, Nat.mul_mod, hdmod] using hm.symm
    have hqeq : q = 2*(q/2)+1 := by omega
    refine ⟨q/2, ?_⟩
    dsimp [f]
    rw [hqeq] at hq
    nlinarith [hh]
  calc
    _ = ∑' k, g (f k) := (hinj.tsum_eq hsupp).symm
    _ = ∑' k : ℕ, (1/(d : ℝ)^2)*(1/(((2*k+1 : ℕ) : ℝ)^2)) := by
      apply tsum_congr
      intro k
      have hdiv : d ∣ 2*f k+1 := ⟨2*k+1, hindex k⟩
      simp only [g, if_pos hdiv, hindex, Nat.cast_mul, mul_pow]
      rw [div_mul_eq_div_div]
      ring
    _ = _ := by
      rw [tsum_mul_left]
      ring


/-- Common squared norm of the normalized positive odd-divisor profiles. -/
def fermiOddHomogeneousMass : ℝ :=
  ∑' m : ℕ, 1 / (((2*m+1 : ℕ) : ℝ)^2)

/-- The coefficient-divisor profile in the actual odd reciprocal-square coordinates. -/
def fermiOddDivisorProfile (d m : ℕ) : ℝ :=
  if d ∣ 2*m+1 then (d : ℝ)/((2*m+1 : ℕ) : ℝ) else 0

theorem fermiOddHomogeneousMass_pos : 0 < fermiOddHomogeneousMass := by
  exact summable_odd_inv_sq.tsum_pos (fun m => by positivity) 0 (by norm_num)

private theorem profile_product (d e m : ℕ) :
    fermiOddDivisorProfile d m*fermiOddDivisorProfile e m =
      (d : ℝ)*e*(if Nat.lcm d e ∣ 2*m+1 then 1/(((2*m+1 : ℕ) : ℝ)^2) else 0) := by
  by_cases hd : d ∣ 2*m+1 <;> by_cases he : e ∣ 2*m+1 <;>
    simp [fermiOddDivisorProfile, Nat.lcm_dvd_iff, hd, he, div_eq_mul_inv, pow_two]
  ring

private theorem summable_odd_multiples (d : ℕ) :
    Summable (fun m : ℕ => if d ∣ 2*m+1 then 1/(((2*m+1 : ℕ) : ℝ)^2) else 0) := by
  apply Summable.of_nonneg_of_le (fun m => by split_ifs <;> positivity) _ summable_odd_inv_sq
  intro m
  split_ifs
  · exact le_rfl
  · positivity

private theorem profile_product_summable (d e : ℕ) :
    Summable (fun m => fermiOddDivisorProfile d m*fermiOddDivisorProfile e m) := by
  exact ((summable_odd_multiples (Nat.lcm d e)).mul_left ((d : ℝ)*e)).congr
    (fun m => (profile_product d e m).symm)

/-- The literal odd-divisor profile Gram kernel is the normalized arithmetic GCD kernel. -/
theorem fermiOddDivisorProfile_gram {d e : ℕ} (hd : Odd d) (he : Odd e) :
    (∑' m : ℕ, fermiOddDivisorProfile d m*fermiOddDivisorProfile e m) =
      fermiOddHomogeneousMass*((Nat.gcd d e : ℝ)^2/((d : ℝ)*e)) := by
  have hodd : Odd (Nat.lcm d e) := (hd.mul he).of_dvd_nat (Nat.lcm_dvd_mul d e)
  have hd0 : d ≠ 0 := by obtain ⟨a,ha⟩ := hd; omega
  have he0 : e ≠ 0 := by obtain ⟨a,ha⟩ := he; omega
  have hl0 : (Nat.lcm d e : ℝ) ≠ 0 := by exact_mod_cast Nat.lcm_ne_zero hd0 he0
  have hg0 : (Nat.gcd d e : ℝ) ≠ 0 := by exact_mod_cast Nat.gcd_ne_zero_left hd0
  have hg : (Nat.gcd d e : ℝ)*(Nat.lcm d e : ℝ) = (d : ℝ)*e := by
    exact_mod_cast Nat.gcd_mul_lcm d e
  have hratio : ((d : ℝ)*e)/(Nat.lcm d e : ℝ)^2 =
      (Nat.gcd d e : ℝ)^2/((d : ℝ)*e) := by
    rw [← hg]
    field_simp [hl0,hg0]
  calc
    _ = ∑' m : ℕ, (d : ℝ)*e*
        (if Nat.lcm d e ∣ 2*m+1 then 1/(((2*m+1 : ℕ) : ℝ)^2) else 0) :=
      tsum_congr (profile_product d e)
    _ = (d : ℝ)*e*(fermiOddHomogeneousMass/(Nat.lcm d e : ℝ)^2) := by
      rw [tsum_mul_left, tsum_oddMultiples_inv_sq hodd]
      rfl
    _ = fermiOddHomogeneousMass*(((d : ℝ)*e)/(Nat.lcm d e : ℝ)^2) := by ring
    _ = _ := by rw [hratio]


/-- A finite coefficient packet in the literal odd-divisor profiles. -/
def fermiOddDivisorPacket (S : Finset ℕ) (c : S → ℝ) (m : ℕ) : ℝ :=
  ∑ d : S, c d*fermiOddDivisorProfile d m

/-- Exact convergent Gram expansion of the odd reciprocal-square packet energy. -/
theorem fermiOddDivisorPacket_energy (S : Finset ℕ)
    (hS : ∀ d ∈ S, Odd d) (c : S → ℝ) :
    Summable (fun m : ℕ => (fermiOddDivisorPacket S c m)^2) ∧
    (∑' m : ℕ, (fermiOddDivisorPacket S c m)^2) =
      fermiOddHomogeneousMass*(∑ d : S, ∑ e : S, gcdSquareRatioMatrix S d e*c d*c e) := by
  let F : S → S → ℕ → ℝ :=
    fun d e m => c d*c e*(fermiOddDivisorProfile d m*fermiOddDivisorProfile e m)
  have hF (d e : S) : Summable (F d e) :=
    (profile_product_summable d e).mul_left (c d*c e)
  have hrow (d : S) : Summable (fun m => ∑ e : S, F d e m) :=
    summable_sum (fun e _ => hF d e)
  have hall : Summable (fun m => ∑ d : S, ∑ e : S, F d e m) :=
    summable_sum (fun d _ => hrow d)
  have hpacket (m : ℕ) : (fermiOddDivisorPacket S c m)^2 =
      ∑ d : S, ∑ e : S, F d e m := by
    rw [fermiOddDivisorPacket, pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    dsimp [F]
    ring
  refine ⟨hall.congr (fun m => (hpacket m).symm), ?_⟩
  calc
    _ = ∑' m : ℕ, ∑ d : S, ∑ e : S, F d e m := tsum_congr hpacket
    _ = ∑ d : S, ∑' m : ℕ, ∑ e : S, F d e m :=
      Summable.tsum_finsetSum (fun d _ => hrow d)
    _ = ∑ d : S, ∑ e : S, ∑' m : ℕ, F d e m := by
      apply Finset.sum_congr rfl
      intro d _
      exact Summable.tsum_finsetSum (fun e _ => hF d e)
    _ = ∑ d : S, ∑ e : S,
        c d*c e*(fermiOddHomogeneousMass*gcdSquareRatioMatrix S d e) := by
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro e _
      dsimp [F]
      rw [tsum_mul_left, fermiOddDivisorProfile_gram (hS d d.2) (hS e e.2)]
      rfl
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      ring

/-- Prime-product frame bounds for the actual odd reciprocal-square energy. -/
theorem fermiOddDivisorPacket_frame_bounds (P S : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hS : ∀ d ∈ S, Odd d)
    (hSP : ∀ d ∈ S, d.primeFactors ⊆ P) (c : S → ℝ) :
    fermiOddHomogeneousMass*(∏ p ∈ P, ((p : ℝ)-1)/((p : ℝ)+1))*(∑ d, (c d)^2) ≤
      (∑' m : ℕ, (fermiOddDivisorPacket S c m)^2) ∧
    (∑' m : ℕ, (fermiOddDivisorPacket S c m)^2) ≤
      fermiOddHomogeneousMass*(∏ p ∈ P, ((p : ℝ)+1)/((p : ℝ)-1))*(∑ d, (c d)^2) := by
  have hp (d : ℕ) (hd : d ∈ S) : 0 < d := by
    obtain ⟨a,ha⟩ := hS d hd
    omega
  have h := gcdSquareRatio_quadratic_bounds P S hP hp hSP c
  rw [(fermiOddDivisorPacket_energy S hS c).2]
  constructor
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h.1 fermiOddHomogeneousMass_pos.le
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h.2 fermiOddHomogeneousMass_pos.le

end GaloisForLFunctions.TransHorizonIncidenceMechanics
