import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic

/-!
# Strong indefiniteness of a visible Suzuki prime Hankel seam

The prime-power part of Suzuki's parity Hankel kernel contains negative atoms

`-Λ(n)n⁻¹ᐟ² δ(x+y-log n)`.

On two reflected packets around one visible seam, such an atom is a weighted swap form.  Its
reflection-even packet is strictly negative and its reflection-odd packet is strictly positive.
Both signs survive every regular perturbation whose quadratic bound is smaller than the seam
weight.  Since packet size is arbitrary, this is the finite algebraic core of the proof that one
visible prime seam makes the literal parity Hankel form strongly indefinite.
-/

namespace RHTower

noncomputable section

abbrev PrimeSeamPacket (m : ℕ) :=
  (Fin m → ℝ) × (Fin m → ℝ)

def primeSeamPacketNormSq {m : ℕ}
    (z : PrimeSeamPacket m) : ℝ :=
  ∑ i, ((z.1 i) ^ 2 + (z.2 i) ^ 2)

def primeSeamAtomQuadratic {m : ℕ}
    (w : ℝ) (z : PrimeSeamPacket m) : ℝ :=
  -2 * w * ∑ i, z.1 i * z.2 i

def primeSeamEvenEmbedding (m : ℕ) :
    (Fin m → ℝ) →ₗ[ℝ] PrimeSeamPacket m :=
  { toFun := fun c => (c, c)
    map_add' := by simp
    map_smul' := by simp }

def primeSeamOddEmbedding (m : ℕ) :
    (Fin m → ℝ) →ₗ[ℝ] PrimeSeamPacket m :=
  { toFun := fun c => (c, -c)
    map_add' := by
      intro c d
      ext <;> simp [add_comm]
    map_smul' := by simp }

theorem primeSeamEvenEmbedding_injective (m : ℕ) :
    Function.Injective (primeSeamEvenEmbedding m) := by
  intro c d h
  exact congrArg Prod.fst h

theorem primeSeamOddEmbedding_injective (m : ℕ) :
    Function.Injective (primeSeamOddEmbedding m) := by
  intro c d h
  exact congrArg Prod.fst h

theorem primeSeamPacketNormSq_even {m : ℕ} (c : Fin m → ℝ) :
    primeSeamPacketNormSq (primeSeamEvenEmbedding m c) =
      2 * ∑ i, (c i) ^ 2 := by
  simp only [primeSeamPacketNormSq, primeSeamEvenEmbedding,
    LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [Finset.sum_add_distrib]
  ring_nf

theorem primeSeamPacketNormSq_odd {m : ℕ} (c : Fin m → ℝ) :
    primeSeamPacketNormSq (primeSeamOddEmbedding m c) =
      2 * ∑ i, (c i) ^ 2 := by
  simp only [primeSeamPacketNormSq, primeSeamOddEmbedding,
    LinearMap.coe_mk, AddHom.coe_mk,
    Pi.neg_apply, neg_sq]
  simp_rw [Finset.sum_add_distrib]
  ring_nf

theorem primeSeamAtomQuadratic_even {m : ℕ}
    (w : ℝ) (c : Fin m → ℝ) :
    primeSeamAtomQuadratic w (primeSeamEvenEmbedding m c) =
      -w * primeSeamPacketNormSq (primeSeamEvenEmbedding m c) := by
  rw [primeSeamPacketNormSq_even]
  simp only [primeSeamAtomQuadratic, primeSeamEvenEmbedding,
    LinearMap.coe_mk, AddHom.coe_mk]
  ring_nf

theorem primeSeamAtomQuadratic_odd {m : ℕ}
    (w : ℝ) (c : Fin m → ℝ) :
    primeSeamAtomQuadratic w (primeSeamOddEmbedding m c) =
      w * primeSeamPacketNormSq (primeSeamOddEmbedding m c) := by
  rw [primeSeamPacketNormSq_odd]
  simp only [primeSeamAtomQuadratic, primeSeamOddEmbedding,
    LinearMap.coe_mk, AddHom.coe_mk, Pi.neg_apply]
  simp_rw [mul_neg, Finset.sum_neg_distrib]
  ring_nf

theorem sum_sq_pos_of_ne_zero {m : ℕ}
    {c : Fin m → ℝ} (hc : c ≠ 0) :
    0 < ∑ i, (c i) ^ 2 := by
  have hex : ∃ i, c i ≠ 0 := by
    by_contra h
    apply hc
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hex
  exact Finset.sum_pos' (fun j _ => sq_nonneg (c j))
    ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩

theorem primeSeamPacketNormSq_even_pos {m : ℕ}
    {c : Fin m → ℝ} (hc : c ≠ 0) :
    0 < primeSeamPacketNormSq (primeSeamEvenEmbedding m c) := by
  rw [primeSeamPacketNormSq_even]
  positivity [sum_sq_pos_of_ne_zero hc]

theorem primeSeamPacketNormSq_odd_pos {m : ℕ}
    {c : Fin m → ℝ} (hc : c ≠ 0) :
    0 < primeSeamPacketNormSq (primeSeamOddEmbedding m c) := by
  rw [primeSeamPacketNormSq_odd]
  positivity [sum_sq_pos_of_ne_zero hc]

def primeSeamPerturbedQuadratic {m : ℕ}
    (w : ℝ) (regular : PrimeSeamPacket m → ℝ)
    (z : PrimeSeamPacket m) : ℝ :=
  primeSeamAtomQuadratic w z + regular z

theorem primeSeamPerturbedQuadratic_even_neg
    {m : ℕ} {w ε : ℝ} (hεw : ε < w)
    (regular : PrimeSeamPacket m → ℝ)
    (hregular : ∀ z, |regular z| ≤ ε * primeSeamPacketNormSq z)
    {c : Fin m → ℝ} (hc : c ≠ 0) :
    primeSeamPerturbedQuadratic w regular
      (primeSeamEvenEmbedding m c) < 0 := by
  let z := primeSeamEvenEmbedding m c
  have hz : 0 < primeSeamPacketNormSq z :=
    primeSeamPacketNormSq_even_pos hc
  have hreg :
      regular z ≤ ε * primeSeamPacketNormSq z :=
    le_trans (le_abs_self _) (hregular z)
  rw [primeSeamPerturbedQuadratic, primeSeamAtomQuadratic_even]
  nlinarith

theorem primeSeamPerturbedQuadratic_odd_pos
    {m : ℕ} {w ε : ℝ} (hεw : ε < w)
    (regular : PrimeSeamPacket m → ℝ)
    (hregular : ∀ z, |regular z| ≤ ε * primeSeamPacketNormSq z)
    {c : Fin m → ℝ} (hc : c ≠ 0) :
    0 < primeSeamPerturbedQuadratic w regular
      (primeSeamOddEmbedding m c) := by
  let z := primeSeamOddEmbedding m c
  have hz : 0 < primeSeamPacketNormSq z :=
    primeSeamPacketNormSq_odd_pos hc
  have hreg :
      -(ε * primeSeamPacketNormSq z) ≤ regular z := by
    have := neg_le_of_abs_le (hregular z)
    simpa only [neg_mul] using this
  rw [primeSeamPerturbedQuadratic, primeSeamAtomQuadratic_odd]
  nlinarith

def suzukiPrimeSeamWeight (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / Real.sqrt n

theorem suzukiPrimeSeamWeight_prime_pos (p : Nat.Primes) :
    0 < suzukiPrimeSeamWeight p := by
  rw [suzukiPrimeSeamWeight,
    ArithmeticFunction.vonMangoldt_apply_prime p.2]
  have hp1 : (1 : ℝ) < (p : ℕ) := by
    exact_mod_cast p.2.one_lt
  exact div_pos (Real.log_pos hp1)
    (Real.sqrt_pos.2 (by exact_mod_cast p.2.pos))

theorem suzukiPrimeSeam_midpoint_in_aperture
    {a : ℝ} (p : Nat.Primes)
    (hvisible : Real.log p < 2 * a) :
    0 < Real.log p / 2 ∧ Real.log p / 2 < a := by
  have hp1 : (1 : ℝ) < (p : ℕ) := by
    exact_mod_cast p.2.one_lt
  constructor
  · positivity [Real.log_pos hp1]
  · linarith

theorem suzukiPrimeSeam_add_smallPerturbation_signedPackets
    (m : ℕ) (p : Nat.Primes) {ε : ℝ}
    (hεw : ε < suzukiPrimeSeamWeight p)
    (regular : PrimeSeamPacket m → ℝ)
    (hregular : ∀ z, |regular z| ≤ ε * primeSeamPacketNormSq z) :
    Function.Injective (primeSeamOddEmbedding m) ∧
    Function.Injective (primeSeamEvenEmbedding m) ∧
    (∀ c ≠ 0, 0 <
      primeSeamPerturbedQuadratic (suzukiPrimeSeamWeight p) regular
        (primeSeamOddEmbedding m c)) ∧
    (∀ c ≠ 0,
      primeSeamPerturbedQuadratic (suzukiPrimeSeamWeight p) regular
        (primeSeamEvenEmbedding m c) < 0) := by
  exact ⟨primeSeamOddEmbedding_injective m,
    primeSeamEvenEmbedding_injective m,
    fun _ hc => primeSeamPerturbedQuadratic_odd_pos
      hεw regular hregular hc,
    fun _ hc => primeSeamPerturbedQuadratic_even_neg
      hεw regular hregular hc⟩

end

end RHTower
