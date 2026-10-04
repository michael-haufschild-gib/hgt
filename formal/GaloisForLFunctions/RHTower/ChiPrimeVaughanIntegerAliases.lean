import GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicPrimeOnlyVaughan
import GaloisForLFunctions.RHTower.ChiPrimePacketFourthMoment
import Mathlib.Algebra.Order.Chebyshev

/-!
# Actual Vaughan prime cofactors have large integer-frequency alias energy

The exact prime-only Vaughan source retains signed short coefficients. On its
prime cofactors above the cutoff those coefficients are literally `-1`. This
file constructs prime bands whose products are injective as integers, yet have
arbitrarily large non-identical-pair energy after reduction modulo each chosen
prime modulus. Congruent products give the same phase at every integer long
factor. Thus real-fraction injectivity cannot identify the sampled diagonal.

This is an unconditional source-coefficient obstruction and a positive prime
family construction. It concerns the prime-cofactor subfamily; it supplies no
lower bound for the full signed cofactor sum or the full Gaussian cubic.
-/

noncomputable section
open Finset ArithmeticFunction Filter
open scoped Topology
namespace RHTower
open Sieve

/-- The prime part of the actual short coefficient has fixed negative sign. -/
theorem vaughanPrimeShort_prime {V p : ℕ} (hV : 1 ≤ V) (hp : p.Prime) (hVp : V < p) :
    vaughanPrimeShort V p = -1 := by
  rw [vaughanPrimeShort, vaughanSquarefreePart, if_pos hp.squarefree]
  change (1 : ArithmeticFunction ℝ) p -
    ((zeta : ArithmeticFunction ℝ) * truncAF (moebius : ArithmeticFunction ℝ) V) p = -1
  rw [coe_zeta_mul_apply, hp.divisors]
  simp [one_apply, hp.ne_one, hp.ne_one.symm, truncAF_apply, hV, not_le.mpr hVp]

/-- Actual dyadic prime family already produced by the source PNT. -/
def vaughanAliasPrimeBand (k : ℕ) : Finset ℕ :=
  (Ioc (64*k^8) (128*k^8)).filter Nat.Prime

/-- Product frequencies with the forbidden q=r contraction removed. -/
def vaughanAliasPairs (k r : ℕ) : Finset (ℕ × ℕ) :=
  (vaughanAliasPrimeBand k).product ((vaughanAliasPrimeBand (2*k^2)).erase r)

/-- Number of pairs carrying one residue of the sampled integer frequency. -/
def vaughanAliasFiber (k r a : ℕ) : ℕ :=
  ((vaughanAliasPairs k r).filter (fun x => x.1*x.2 % r = a)).card

/-- Exact same-residue energy with the identical-tuple contribution removed. -/
def vaughanAliasOffDiagonal (k r : ℕ) : ℝ :=
  (∑ a ∈ range r, (vaughanAliasFiber k r a : ℝ)^2) - (vaughanAliasPairs k r).card

private theorem alias_fiber_sum (k : ℕ) {r : ℕ} (hr : 0 < r) :
    (∑ a ∈ range r, vaughanAliasFiber k r a) = (vaughanAliasPairs k r).card := by
  symm
  exact Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_range.mpr (Nat.mod_lt _ hr))

private theorem alias_energy_lower (k : ℕ) {r : ℕ} (hr : 0 < r)
    (hc : (k+1)*r ≤ (vaughanAliasPairs k r).card) :
    (k : ℝ) * (vaughanAliasPairs k r).card ≤ vaughanAliasOffDiagonal k r := by
  have hsum : (∑ a ∈ range r, (vaughanAliasFiber k r a : ℝ)) =
      (vaughanAliasPairs k r).card := by exact_mod_cast alias_fiber_sum k hr
  have hs := sq_sum_le_card_mul_sum_sq (s := range r)
    (f := fun a => (vaughanAliasFiber k r a : ℝ))
  rw [hsum, card_range] at hs
  have hcR : ((k : ℝ)+1)*r ≤ (vaughanAliasPairs k r).card := by exact_mod_cast hc
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hmR : (0 : ℝ) ≤ (vaughanAliasPairs k r).card := Nat.cast_nonneg _
  have hm := mul_le_mul_of_nonneg_right hcR hmR
  unfold vaughanAliasOffDiagonal
  nlinarith

private theorem alias_count_arith {k : ℕ} (hk : 1 ≤ k) :
    (k+1) * (128*(2*k^2)^8) ≤ (64*k^7)*(32*(2*k^2)^7) := by
  have hp : k ≤ k^5 := Nat.le_self_pow (by omega) k
  have hs : k+1 ≤ 8*k^5 := by omega
  have hm := Nat.mul_le_mul_right (256*k^2*(2*k^2)^7) hs
  nlinarith only [hm]

/-- All chosen prime moduli carry more actual negative prime-cofactor pairs
than residue classes, by an arbitrarily growing factor. -/
theorem eventually_vaughanAliasPairs_card :
    ∀ᶠ k : ℕ in atTop, ∀ r ∈ vaughanAliasPrimeBand (2*k^2),
      (k+1)*r ≤ (vaughanAliasPairs k r).card := by
  have ht : Tendsto (fun k : ℕ => 2*k^2) atTop atTop := by
    apply tendsto_atTop_mono (fun k => ?_) tendsto_id
    have hh : k ≤ k^2 := Nat.le_self_pow (by omega) k
    change k ≤ 2*k^2
    omega
  filter_upwards [eventually_prime_packet_dyadic_count,
    ht.eventually eventually_prime_packet_dyadic_count,
    eventually_ge_atTop (1:ℕ)] with k hk hlarge hk1
  intro r hr
  have hrc := (mem_Ioc.mp (mem_filter.mp hr).1).2
  change 64*k^7 ≤ (vaughanAliasPrimeBand k).card at hk
  change 64*(2*k^2)^7 ≤ (vaughanAliasPrimeBand (2*k^2)).card at hlarge
  have hpos : 1 ≤ (2*k^2)^7 := one_le_pow₀ (by nlinarith)
  have hq : 32*(2*k^2)^7 ≤ ((vaughanAliasPrimeBand (2*k^2)).erase r).card := by
    rw [card_erase_of_mem hr]
    omega
  change (k+1)*r ≤ ((vaughanAliasPrimeBand k).product _).card
  have he := Finset.card_product (vaughanAliasPrimeBand k) ((vaughanAliasPrimeBand (2*k^2)).erase r)
  change ((vaughanAliasPrimeBand k).product _).card = _ at he
  rw [he]
  exact (Nat.mul_le_mul_left (k+1) hrc).trans
    ((alias_count_arith hk1).trans (Nat.mul_le_mul hk hq))

/-- Actual signed prime-cofactor aliases dominate their identical-tuple energy
by every prescribed growing factor. No phase estimate or prime-count premise is assumed. -/
theorem eventually_vaughanAliasOffDiagonal_large :
    ∀ᶠ k : ℕ in atTop, ∀ r ∈ vaughanAliasPrimeBand (2*k^2),
      (k : ℝ) * (vaughanAliasPairs k r).card ≤ vaughanAliasOffDiagonal k r := by
  filter_upwards [eventually_vaughanAliasPairs_card] with k hk
  intro r hr
  exact alias_energy_lower k (mem_filter.mp hr).2.pos (hk r hr)

/-- Every cofactor used above has the literal short-source value -1. -/
theorem vaughanAliasPairs_coefficient {k r : ℕ} (hk : 1 ≤ k)
    {x : ℕ × ℕ} (hx : x ∈ vaughanAliasPairs k r) :
    vaughanPrimeShort (64*k^8) x.1 = -1 := by
  have hm := (mem_product.mp hx).1
  exact vaughanPrimeShort_prime (by have hh := one_le_pow₀ hk (n := 8); omega) (mem_filter.mp hm).2
    (mem_Ioc.mp (mem_filter.mp hm).1).1

/-- In each residue fibre the actual signed cofactor sum is minus its size. -/
theorem vaughanAliasFiber_signed_sum {k : ℕ} (hk : 1 ≤ k) (r a : ℕ) :
    (∑ x ∈ (vaughanAliasPairs k r).filter (fun x => x.1*x.2 % r = a),
      vaughanPrimeShort (64*k^8) x.1) = -(vaughanAliasFiber k r a : ℝ) := by
  rw [show (∑ x ∈ (vaughanAliasPairs k r).filter (fun x => x.1*x.2 % r = a),
      vaughanPrimeShort (64*k^8) x.1) =
      ∑ _x ∈ (vaughanAliasPairs k r).filter (fun x => x.1*x.2 % r = a), (-1 : ℝ) by
    apply Finset.sum_congr rfl
    intro x hx
    exact vaughanAliasPairs_coefficient hk (mem_filter.mp hx).1]
  simp [vaughanAliasFiber]

/-- The large alias mass is the off-diagonal energy of the actual signed
Vaughan coefficients, not a coefficient-free count substituted for them. -/
theorem vaughanAliasOffDiagonal_eq_signed {k : ℕ} (hk : 1 ≤ k) (r : ℕ) :
    vaughanAliasOffDiagonal k r =
      (∑ a ∈ range r,
        (∑ x ∈ (vaughanAliasPairs k r).filter (fun x => x.1*x.2 % r = a),
          vaughanPrimeShort (64*k^8) x.1)^2) -
      ∑ x ∈ vaughanAliasPairs k r, (vaughanPrimeShort (64*k^8) x.1)^2 := by
  simp_rw [vaughanAliasFiber_signed_sum hk, neg_sq]
  have hd : (∑ x ∈ vaughanAliasPairs k r, (vaughanPrimeShort (64*k^8) x.1)^2) =
      ((vaughanAliasPairs k r).card : ℝ) := by
    calc
      _ = ∑ _x ∈ vaughanAliasPairs k r, (1:ℝ) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [vaughanAliasPairs_coefficient hk hx]
        norm_num
      _ = _ := by simp
  rw [hd]
  rfl

private theorem alias_band_separation {k : ℕ} (hk : 1 ≤ k)
    {m q : ℕ} (hm : m ∈ vaughanAliasPrimeBand k)
    (hq : q ∈ vaughanAliasPrimeBand (2*k^2)) : m < q := by
  have hmU := (mem_Ioc.mp (mem_filter.mp hm).1).2
  have hqL := (mem_Ioc.mp (mem_filter.mp hq).1).1
  have h8 : 1 ≤ k^8 := one_le_pow₀ hk
  have h16 : k^8 ≤ k^16 := by
    calc
      k^8 ≤ k^8 * k^8 := Nat.le_mul_of_pos_right _ (by omega)
      _ = k^16 := by ring
  have hscale : 128*k^8 < 64*(2*k^2)^8 := by
    have he : (2*k^2)^8 = 256*k^16 := by ring
    rw [he]
    omega
  omega

/-- The products, and hence their real fractions at fixed r, are distinct.
This does not imply distinct integer-sampled phases. -/
theorem vaughanAliasPairs_product_injective {k r : ℕ} (hk : 1 ≤ k) :
    Set.InjOn (fun x : ℕ × ℕ => x.1*x.2) (vaughanAliasPairs k r) := by
  intro x hx y hy he
  have hxP := (mem_product.mp hx).1
  have hyP := (mem_product.mp hy).1
  have hxQ := (mem_erase.mp (mem_product.mp hx).2).2
  have hyQ := (mem_erase.mp (mem_product.mp hy).2).2
  have hxq := (mem_filter.mp hxQ).2
  have hyq := (mem_filter.mp hyQ).2
  have hprod : x.1*x.2 = y.1*y.2 := he
  have hd : x.2 ∣ y.1*y.2 := by
    rw [← hprod]
    exact Nat.dvd_mul_left _ _
  have hnot : ¬x.2 ∣ y.1 := fun h =>
    (Nat.le_of_dvd (mem_filter.mp hyP).2.pos h).not_gt (alias_band_separation hk hyP hxQ)
  have heq : x.2 = y.2 := (Nat.prime_dvd_prime_iff_eq hxq hyq).mp
    ((hxq.dvd_mul.mp hd).resolve_left hnot)
  exact Prod.ext (Nat.mul_left_cancel hyq.pos (by simpa [heq, mul_comm] using he)) heq

/-- Every sampled frequency is a unit at its actual prime modulus. -/
theorem vaughanAliasPairs_not_dvd {k r : ℕ} (hk : 1 ≤ k)
    (hr : r ∈ vaughanAliasPrimeBand (2*k^2))
    {x : ℕ × ℕ} (hx : x ∈ vaughanAliasPairs k r) : ¬r ∣ x.1*x.2 := by
  have hp := (mem_filter.mp hr).2
  have hxP := (mem_product.mp hx).1
  have hxQ := mem_erase.mp (mem_product.mp hx).2
  apply hp.not_dvd_mul
  · exact fun h => (Nat.le_of_dvd (mem_filter.mp hxP).2.pos h).not_gt
      (alias_band_separation hk hxP hr)
  · exact fun h => hxQ.1 ((Nat.prime_dvd_prime_iff_eq hp (mem_filter.mp hxQ.2).2).mp h).symm

private theorem alias_phase_mod (d K : ℕ) {r : ℕ} (hr : 0 < r) :
    Complex.exp (2*Real.pi*Complex.I*(d:ℂ)*(K:ℂ)/r) =
      Complex.exp (2*Real.pi*Complex.I*(d:ℂ)*(K%r:ℕ)/r) := by
  have hr0 : (r:ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hK : (K:ℂ) = (r:ℂ)*(K/r:ℕ)+(K%r:ℕ) := by
    exact_mod_cast (Nat.div_add_mod K r).symm
  have he : 2*Real.pi*Complex.I*(d:ℂ)*(K:ℂ)/r =
      ((d*(K/r):ℕ):ℂ)*(2*Real.pi*Complex.I) +
        2*Real.pi*Complex.I*(d:ℂ)*(K%r:ℕ)/r := by
    rw [hK]
    push_cast
    field_simp
  rw [he, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, one_mul]

/-- Congruent product residues are EXACTLY phase-aligned at every integer
long factor, even when their real fractions are unequal. -/
theorem vaughanAlias_phase_eq {r : ℕ} (hr : 0 < r) {x y : ℕ × ℕ}
    (h : x.1*x.2 % r = y.1*y.2 % r) (d : ℕ) :
    bourgainOscillation (2*Real.pi*((d:ℝ)*x.1*x.2/r)) =
      bourgainOscillation (2*Real.pi*((d:ℝ)*y.1*y.2/r)) := by
  have he (z : ℕ × ℕ) : bourgainOscillation (2*Real.pi*((d:ℝ)*z.1*z.2/r)) =
      Complex.exp (2*Real.pi*Complex.I*(d:ℂ)*(z.1*z.2:ℕ)/r) := by
    unfold bourgainOscillation
    congr 1
    push_cast
    ring
  rw [he, he]
  calc
    _ = Complex.exp (2*Real.pi*Complex.I*(d:ℂ)*(x.1*x.2%r:ℕ)/r) :=
      alias_phase_mod d _ hr
    _ = Complex.exp (2*Real.pi*Complex.I*(d:ℂ)*(y.1*y.2%r:ℕ)/r) := by rw [h]
    _ = _ := (alias_phase_mod d _ hr).symm

/-- The constructed moduli and exact, nontrivial source aliases exist
unconditionally. Their products differ, all their actual short coefficients
are -1, and all integer long factors give identical phases. -/
theorem eventually_exists_vaughanPrimeAlias :
    ∀ᶠ k : ℕ in atTop, ∃ r ∈ vaughanAliasPrimeBand (2*k^2),
      ∃ x ∈ vaughanAliasPairs k r, ∃ y ∈ vaughanAliasPairs k r,
        x.1*x.2 ≠ y.1*y.2 ∧
        vaughanPrimeShort (64*k^8) x.1 = -1 ∧
        vaughanPrimeShort (64*k^8) y.1 = -1 ∧
        (∀ d : ℕ, bourgainOscillation (2*Real.pi*((d:ℝ)*x.1*x.2/r)) =
          bourgainOscillation (2*Real.pi*((d:ℝ)*y.1*y.2/r))) ∧
        (k:ℝ)*(vaughanAliasPairs k r).card ≤ vaughanAliasOffDiagonal k r := by
  have ht : Tendsto (fun k : ℕ => 2*k^2) atTop atTop := by
    apply tendsto_atTop_mono (fun k => ?_) tendsto_id
    change k ≤ 2*k^2
    have hh : k ≤ k^2 := Nat.le_self_pow (by omega) k
    omega
  filter_upwards [eventually_vaughanAliasPairs_card,
    eventually_vaughanAliasOffDiagonal_large,
    ht.eventually eventually_prime_packet_dyadic_count,
    eventually_ge_atTop (1:ℕ)] with k hc he hp hk
  have hrne : (vaughanAliasPrimeBand (2*k^2)).Nonempty := by
    apply Finset.card_pos.mp
    change 64*(2*k^2)^7 ≤ (vaughanAliasPrimeBand (2*k^2)).card at hp
    have hp0 : 0 < 64*(2*k^2)^7 := by positivity
    omega
  obtain ⟨r,hr⟩ := hrne
  have hr0 := (mem_filter.mp hr).2.pos
  have hlt : (range r).card < (vaughanAliasPairs k r).card := by
    rw [card_range]
    have hh := hc r hr
    nlinarith
  obtain ⟨x,hx,y,hy,hxy,hmod⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt
    (fun x _ => Finset.mem_range.mpr (Nat.mod_lt (x.1*x.2) hr0))
  exact ⟨r,hr,x,hx,y,hy,(fun hprod => hxy (vaughanAliasPairs_product_injective hk hx hy hprod)),
    vaughanAliasPairs_coefficient hk hx, vaughanAliasPairs_coefficient hk hy,
    vaughanAlias_phase_eq hr0 hmod, he r hr⟩


/-- No fixed multiple of identical-tuple energy controls this actual
prime-cofactor subfamily on all sufficiently large scales. -/
theorem not_eventually_vaughanAliasOffDiagonal_le_card :
    ¬ ∃ C : ℝ, ∀ᶠ k : ℕ in atTop,
      ∀ r ∈ vaughanAliasPrimeBand (2*k^2),
        vaughanAliasOffDiagonal k r ≤ C*(vaughanAliasPairs k r).card := by
  rintro ⟨C,hC⟩
  obtain ⟨K,hK⟩ := exists_nat_gt C
  have hh := eventually_exists_vaughanPrimeAlias.and (hC.and (eventually_ge_atTop K))
  obtain ⟨k,hk,hCk,hKk⟩ := hh.exists
  obtain ⟨r,hr,x,hx,y,hy,hprod,hcx,hcy,hphase,henergy⟩ := hk
  have hcard : (0:ℝ) < (vaughanAliasPairs k r).card := by
    exact_mod_cast Finset.card_pos.mpr ⟨x,hx⟩
  have hkR : (K:ℝ) ≤ k := by exact_mod_cast hKk
  have hupper := hCk r hr
  nlinarith

end RHTower
