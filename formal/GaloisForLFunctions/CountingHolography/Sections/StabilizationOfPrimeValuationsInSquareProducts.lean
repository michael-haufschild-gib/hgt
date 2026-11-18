import GaloisForLFunctions.CountingHolography.Sections.SquareGeneratorPrefix
import GaloisForLFunctions.CountingHolography.Sections.ReducedOrdinaryPrimeProducts

/-!
# Stabilization of the large prime valuations of square-generator products

Outside the fixed short-lag range, a nonzero sampled prime row requires
the lower label to be one. Its upper label then pins the root to a
fixed interval proportional to the square root of the prime.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset AbsoluteGeometryOfSpecZ _root_.RHTower

private abbrev q (n m : ℕ) := ordinaryPrimeGenerator (m • successorSquareTriple n)

/-- Every large lag with nonzero valuation lies within a fixed factor of n²,
uniformly in the multiplicity of the triple. -/
theorem square_generator_valuation_support : ∃ D : ℝ, 1 ≤ D ∧
    ∀ {n p : ℕ}, 0 < n → 9*D < p → ∀ m : ℕ,
      deningerRatExp (ordinaryPrimeGenerator (m • successorSquareTriple n)) p ≠ 0 →
      (n:ℝ)^2 ≤ D*p ∧ (p:ℝ) ≤ 9*D*(n:ℝ)^2 := by
  obtain ⟨D,hD,hraw⟩ := contactMultiplicity_support
  refine ⟨D,hD,fun {n p} hn hp m he => ?_⟩
  let a := m • successorSquareTriple n
  let N := (2*n+1)^2+1
  have hz : contactMultiplicity (packet a) (3*windowEnd N) (resolution a) p ≠ 0 := by
    intro hzero
    apply he
    rw [ordinaryPrimeGenerator_exponent]
    change (if p ∈ (Icc 2 (3*windowEnd N)).filter Nat.Prime then
      ⌊contactMultiplicity (packet a) (3*windowEnd N) (resolution a) p⌋ else 0)=0
    simp [hzero]
  obtain ⟨i,j,hi,hj,hij,hji⟩ := hraw N a _ _ p hz
  let x := (n:ℝ)^2
  let y := ((2*n+1:ℕ):ℝ)^2
  have hx : (1:ℝ) ≤ x := one_le_pow₀ (by exact_mod_cast hn : (1:ℝ) ≤ n)
  have hxy : x ≤ y := pow_le_pow_left₀ (Nat.cast_nonneg n)
    (by exact_mod_cast (by omega : n ≤ 2*n+1)) 2
  have hy : y ≤ 9*x := by
    have h := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 2*(n:ℝ)+1)
      (show 2*(n:ℝ)+1 ≤ 3*n by linarith only [show (1:ℝ) ≤ n by exact_mod_cast hn]) 2
    dsimp only [x,y]
    push_cast
    linarith only [h]
  have labels {k : Fin N} (hk : a k ≠ 0) : (k:ℝ)+1=1 ∨ (x ≤ (k:ℝ)+1 ∧ (k:ℝ)+1 ≤ y) := by
    have h : successorSquareTriple n k ≠ 0 := fun h => hk (by simp [a,Pi.smul_apply,h])
    rcases successorSquareTriple_support hn h with h' | h' | h'
    · exact Or.inl h'
    · right; rw [h']; exact ⟨le_rfl,hxy⟩
    · right; rw [h']; exact ⟨hxy,le_rfl⟩
  have hjy : (j:ℝ)+1 ≤ y := (labels hj).elim (fun h => by rw [h]; exact hx.trans hxy) And.right
  have hD₀ := zero_le_one.trans hD
  have hbound := hij.trans (mul_le_mul_of_nonneg_left (hjy.trans hy) hD₀)
  have hi₁ : (i:ℝ)+1=1 := by
    rcases labels hi with h | h
    · exact h
    · have hpx := (mul_le_mul_of_nonneg_left h.1 (Nat.cast_nonneg p)).trans hbound
      have hstrict := mul_lt_mul_of_pos_right hp (zero_lt_one.trans_le hx)
      linarith only [hpx,hstrict]
  rw [hi₁,mul_one] at hbound hji
  have hjx : x ≤ (j:ℝ)+1 := by
    rcases labels hj with h | h
    · rw [hi₁,h,mul_one,mul_one] at hij
      linarith only [hij,hp,hD]
    · exact h.1
  exact ⟨hjx.trans hji,hbound.trans_eq (by dsimp only [x]; ring)⟩

/-- Prime valuation of the reduced prefix, with cancellation across conductors. -/
theorem squareGeneratorPrefix_valuation (p N : ℕ) : deningerRatExp (squareGeneratorPrefix N) p =
    ∑ j ∈ Ioc 0 N, deningerRatExp (ordinaryPrimeGenerator (j • successorSquareTriple j)) p := by
  have hpos (j : ℕ) : 0 < q j j :=
    prod_pos fun k _ => zpow_pos (Nat.cast_pos.mpr (contactBase_pos k)) _
  unfold squareGeneratorPrefix
  rw [deningerRatExp_prod (fun j _ => (hpos j).ne'),Finsupp.finsetSum_apply]

/-- The actual reduced prefix has a constant p-adic valuation after its
root passes √(Dp), simultaneously for all primes larger than 9D. -/
theorem large_prime_valuation_of_square_prefix_stabilizes : ∃ D : ℝ, 1 ≤ D ∧
    ∀ {p M N : ℕ}, 9*D < p → Real.sqrt (D*p) ≤ M → M ≤ N →
      deningerRatExp (squareGeneratorPrefix N) p = deningerRatExp (squareGeneratorPrefix M) p := by
  obtain ⟨D,hD,h⟩ := square_generator_valuation_support
  refine ⟨D,hD,fun {p M N} hp hcut hMN => ?_⟩
  rw [squareGeneratorPrefix_valuation,squareGeneratorPrefix_valuation]
  have hsub : Ioc 0 M ⊆ Ioc 0 N := fun j hj =>
    mem_Ioc.mpr ⟨(mem_Ioc.mp hj).1,(mem_Ioc.mp hj).2.trans hMN⟩
  apply (sum_subset hsub ?_).symm
  intro j hj hout
  by_contra he
  have hj' : M < j := lt_of_not_ge fun hM => hout (mem_Ioc.mpr ⟨(mem_Ioc.mp hj).1,hM⟩)
  have hs := Real.sqrt_le_sqrt (h (mem_Ioc.mp hj).1 hp j he).1
  rw [Real.sqrt_sq (Nat.cast_nonneg j)] at hs
  exact (Nat.cast_lt.mpr hj' : (M:ℝ) < j).not_ge (hs.trans hcut)

#print axioms large_prime_valuation_of_square_prefix_stabilizes
#print axioms square_generator_valuation_support

end GaloisForLFunctions.CountingHolography.Sections
