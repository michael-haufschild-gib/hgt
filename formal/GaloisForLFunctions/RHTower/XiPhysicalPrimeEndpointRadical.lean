import GaloisForLFunctions.RHTower.XiPhysicalPrimeEndpointNoncancellation
import GaloisForLFunctions.RHTower.CCMPhysicalPrimeApertureCharacterTomography
import GaloisForLFunctions.RHTower.XiPhysicalPrimeLogApertureDispersion
import GaloisForLFunctions.HTGeometry.ZeroEstimate

/-!
# Physical prime endpoint radical

The finite physical endpoint measure has a nonzero arithmetic jump. Finite Vandermonde separation
on the aperture circle exposes a nonzero Fourier channel, hence the coherent centered aperture
carrier cannot vanish. This proves the exact active-packet radical `(PE9)` and strict normalized
dispersion `(AH16)` under `0 < k - m < A`.
-/

open scoped BigOperators
open MeasureTheory Set Complex

namespace RHTower

noncomputable section

/-- Endpoint viewed on the additive aperture circle. -/
def xiPhysicalPrimeLogEndpointNode (A t : ℝ) : AddCircle A := t

/-- Total complex end weight at an aperture-circle node. -/
def xiPhysicalPrimeLogEndpointCircleEndWeight
    (P : Finset Nat.Primes) (A k : ℝ) (x : AddCircle A) : ℂ :=
  ∑ p ∈ P, if xiPhysicalPrimeLogEndpointNode A
      (xiPhysicalPrimeLogApertureEnd A k p) = x then
    (physicalPrimeEndpointWeight p : ℂ) else 0

/-- Total complex start weight at an aperture-circle node. -/
def xiPhysicalPrimeLogEndpointCircleStartWeight
    (P : Finset Nat.Primes) (A m : ℝ) (x : AddCircle A) : ℂ :=
  ∑ p ∈ P, if xiPhysicalPrimeLogEndpointNode A
      (xiPhysicalPrimeLogApertureStart m p) = x then
    (physicalPrimeEndpointWeight p : ℂ) else 0

/-- Signed endpoint coefficient after identifying the two aperture boundary points. -/
def xiPhysicalPrimeLogEndpointCircleJump
    (P : Finset Nat.Primes) (A m k : ℝ) (x : AddCircle A) : ℂ :=
  xiPhysicalPrimeLogEndpointCircleEndWeight P A k x -
    xiPhysicalPrimeLogEndpointCircleStartWeight P A m x

/-- Finite support of the endpoint measure on the aperture circle. -/
def xiPhysicalPrimeLogEndpointNodeSet
    (P : Finset Nat.Primes) (A m k : ℝ) : Finset (AddCircle A) :=
  P.image (fun p => xiPhysicalPrimeLogEndpointNode A
      (xiPhysicalPrimeLogApertureEnd A k p)) ∪
    P.image (fun p => xiPhysicalPrimeLogEndpointNode A
      (xiPhysicalPrimeLogApertureStart m p))

private theorem active_endpoint_mem_intervals
    {A m k : ℝ} {p : Nat.Primes}
    (hactive : 0 < xiPhysicalPrimeLogApertureLength A m k p) :
    xiPhysicalPrimeLogApertureStart m p ∈ Ico 0 A ∧
      xiPhysicalPrimeLogApertureEnd A k p ∈ Ioc 0 A := by
  have hdiff : xiPhysicalPrimeLogApertureStart m p <
      xiPhysicalPrimeLogApertureEnd A k p := by
    have : 0 < xiPhysicalPrimeLogApertureEnd A k p -
        xiPhysicalPrimeLogApertureStart m p := by
      simpa [xiPhysicalPrimeLogApertureLength] using hactive
    linarith
  have hs0 := xiPhysicalPrimeLogApertureStart_nonneg m p
  have heA := xiPhysicalPrimeLogApertureEnd_le A k p
  exact ⟨⟨hs0, hdiff.trans_le heA⟩, ⟨lt_of_le_of_lt hs0 hdiff, heA⟩⟩

/-- At an interior real endpoint, circle aggregation agrees with the literal signed jump. -/
theorem xiPhysicalPrimeLogEndpointCircleJump_at_interior
    {P : Finset Nat.Primes} {A m k t : ℝ}
    (hA : 0 < A)
    (hactive : ∀ p ∈ P, 0 < xiPhysicalPrimeLogApertureLength A m k p)
    (ht0 : 0 < t) (htA : t < A) :
    xiPhysicalPrimeLogEndpointCircleJump P A m k
        (xiPhysicalPrimeLogEndpointNode A t) =
      (xiPhysicalPrimeLogEndpointJump P A m k t : ℂ) := by
  letI : Fact (0 < A) := ⟨hA⟩
  have htIco : t ∈ Ico (0 : ℝ) (0 + A) := by simpa using ⟨ht0.le, htA⟩
  have htIoc : t ∈ Ioc (0 : ℝ) (0 + A) := by simpa using ⟨ht0, htA.le⟩
  rw [xiPhysicalPrimeLogEndpointCircleJump,
    xiPhysicalPrimeLogEndpointJump,
    xiPhysicalPrimeLogEndpointCircleEndWeight,
    xiPhysicalPrimeLogEndpointCircleStartWeight,
    xiPhysicalPrimeLogEndpointEndWeight,
    xiPhysicalPrimeLogEndpointStartWeight]
  push_cast
  congr 1
  · apply Finset.sum_congr rfl
    intro p hp
    have heIoc : xiPhysicalPrimeLogApertureEnd A k p ∈
        Ioc (0 : ℝ) (0 + A) := by
      simpa using (active_endpoint_mem_intervals (hactive p hp)).2
    have heiff : xiPhysicalPrimeLogEndpointNode A
          (xiPhysicalPrimeLogApertureEnd A k p) =
          xiPhysicalPrimeLogEndpointNode A t ↔
        xiPhysicalPrimeLogApertureEnd A k p = t := by
      simpa only [xiPhysicalPrimeLogEndpointNode] using
        (AddCircle.coe_eq_coe_iff_of_mem_Ioc heIoc htIoc)
    by_cases heq : xiPhysicalPrimeLogApertureEnd A k p = t <;>
      simp [heiff, heq]
  · apply Finset.sum_congr rfl
    intro p hp
    have hsIco : xiPhysicalPrimeLogApertureStart m p ∈
        Ico (0 : ℝ) (0 + A) := by
      simpa using (active_endpoint_mem_intervals (hactive p hp)).1
    have hsiff : xiPhysicalPrimeLogEndpointNode A
          (xiPhysicalPrimeLogApertureStart m p) =
          xiPhysicalPrimeLogEndpointNode A t ↔
        xiPhysicalPrimeLogApertureStart m p = t := by
      simpa only [xiPhysicalPrimeLogEndpointNode] using
        (AddCircle.coe_eq_coe_iff_of_mem_Ico hsIco htIco)
    by_cases heq : xiPhysicalPrimeLogApertureStart m p = t <;>
      simp [hsiff, heq]

private theorem endpoint_node_mem_nodeSet_end
    {P : Finset Nat.Primes} {A m k : ℝ} {p : Nat.Primes} (hp : p ∈ P) :
    xiPhysicalPrimeLogEndpointNode A (xiPhysicalPrimeLogApertureEnd A k p) ∈
      xiPhysicalPrimeLogEndpointNodeSet P A m k := by
  rw [xiPhysicalPrimeLogEndpointNodeSet]
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)

private theorem endpoint_node_mem_nodeSet_start
    {P : Finset Nat.Primes} {A m k : ℝ} {p : Nat.Primes} (hp : p ∈ P) :
    xiPhysicalPrimeLogEndpointNode A (xiPhysicalPrimeLogApertureStart m p) ∈
      xiPhysicalPrimeLogEndpointNodeSet P A m k := by
  rw [xiPhysicalPrimeLogEndpointNodeSet]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)

private theorem sum_grouped_endpoint_nodes
    {P : Finset Nat.Primes} {A m k : ℝ}
    (node : Nat.Primes → AddCircle A)
    (hnode : ∀ p ∈ P, node p ∈ xiPhysicalPrimeLogEndpointNodeSet P A m k)
    (f : AddCircle A → ℂ) :
    ∑ x ∈ xiPhysicalPrimeLogEndpointNodeSet P A m k,
        (∑ p ∈ P, if node p = x then
          (physicalPrimeEndpointWeight p : ℂ) else 0) * f x =
      ∑ p ∈ P, (physicalPrimeEndpointWeight p : ℂ) * f (node p) := by
  classical
  calc
    ∑ x ∈ xiPhysicalPrimeLogEndpointNodeSet P A m k,
        (∑ p ∈ P, if node p = x then
          (physicalPrimeEndpointWeight p : ℂ) else 0) * f x =
      ∑ x ∈ xiPhysicalPrimeLogEndpointNodeSet P A m k,
        ∑ p ∈ P, (if node p = x then
          (physicalPrimeEndpointWeight p : ℂ) else 0) * f x := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.sum_mul]
    _ = ∑ p ∈ P, ∑ x ∈ xiPhysicalPrimeLogEndpointNodeSet P A m k,
        (if node p = x then (physicalPrimeEndpointWeight p : ℂ) else 0) * f x := by
      rw [Finset.sum_comm]
    _ = ∑ p ∈ P, (physicalPrimeEndpointWeight p : ℂ) * f (node p) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_eq_single (node p)]
      · simp
      · intro x hx hxp
        simp [hxp.symm]
      · simp [hnode p hp]

/-- Grouping prime endpoints by aperture-circle node preserves every character moment. -/
theorem sum_endpointCircleJump_mul
    (P : Finset Nat.Primes) (A m k : ℝ) (f : AddCircle A → ℂ) :
    ∑ x ∈ xiPhysicalPrimeLogEndpointNodeSet P A m k,
        xiPhysicalPrimeLogEndpointCircleJump P A m k x * f x =
      ∑ p ∈ P, (physicalPrimeEndpointWeight p : ℂ) *
        (f (xiPhysicalPrimeLogEndpointNode A
            (xiPhysicalPrimeLogApertureEnd A k p)) -
          f (xiPhysicalPrimeLogEndpointNode A
            (xiPhysicalPrimeLogApertureStart m p))) := by
  classical
  simp_rw [xiPhysicalPrimeLogEndpointCircleJump]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  simp_rw [xiPhysicalPrimeLogEndpointCircleEndWeight,
    xiPhysicalPrimeLogEndpointCircleStartWeight]
  rw [sum_grouped_endpoint_nodes
      (fun p => xiPhysicalPrimeLogEndpointNode A
        (xiPhysicalPrimeLogApertureEnd A k p))
      (fun p hp => endpoint_node_mem_nodeSet_end hp) f,
    sum_grouped_endpoint_nodes
      (fun p => xiPhysicalPrimeLogEndpointNode A
        (xiPhysicalPrimeLogApertureStart m p))
      (fun p hp => endpoint_node_mem_nodeSet_start hp) f]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- Multiplying one active interval moment by its nonzero character rate exposes its two signed
endpoint characters. -/
theorem xiPhysicalApertureCharacterRate_mul_characterMoment
    {A m k : ℝ} (hA : 0 < A) {n : ℤ} (hn : n ≠ 0)
    (p : Nat.Primes)
    (hactive : 0 < xiPhysicalPrimeLogApertureLength A m k p) :
    xiPhysicalApertureCharacterRate A n *
        xiPhysicalPrimeLogCharacterMoment A n m k p =
      fourier n (xiPhysicalPrimeLogEndpointNode A
        (xiPhysicalPrimeLogApertureEnd A k p)) -
      fourier n (xiPhysicalPrimeLogEndpointNode A
        (xiPhysicalPrimeLogApertureStart m p)) := by
  let s := xiPhysicalPrimeLogApertureStart m p
  let e := xiPhysicalPrimeLogApertureEnd A k p
  let L := xiPhysicalPrimeLogApertureLength A m k p
  let r := xiPhysicalApertureCharacterRate A n
  have hr : r ≠ 0 := xiPhysicalApertureCharacterRate_ne_zero hA hn
  have hdiff : 0 < e - s := by
    simpa [e, s, L, xiPhysicalPrimeLogApertureLength] using hactive
  have hL : L = e - s := by
    change xiPhysicalPrimeLogApertureLength A m k p = e - s
    rw [xiPhysicalPrimeLogApertureLength, max_eq_right hdiff.le]
  have hSL : s + L = e := by linarith
  have hexp : Complex.exp ((e : ℂ) * r) *
      Complex.exp (-((L : ℂ) * r)) =
      Complex.exp ((s : ℂ) * r) := by
    rw [← Complex.exp_add]
    congr 1
    rw [hL]
    push_cast
    ring
  rw [xiPhysicalPrimeLogCharacterMoment,
    rectangularWindowAmplitude_eq_div hr]
  rw [show fourier n (xiPhysicalPrimeLogEndpointNode A e) =
      Complex.exp (r * (e : ℂ)) by
        simpa [xiPhysicalPrimeLogEndpointNode, r] using
          fourier_coe_eq_xiPhysicalApertureCharacterExp hA n e,
    show fourier n (xiPhysicalPrimeLogEndpointNode A s) =
      Complex.exp (r * (s : ℂ)) by
        simpa [xiPhysicalPrimeLogEndpointNode, r] using
          fourier_coe_eq_xiPhysicalApertureCharacterExp hA n s]
  change xiPhysicalApertureCharacterRate A n *
      (Complex.exp (((xiPhysicalPrimeLogApertureStart m p +
          xiPhysicalPrimeLogApertureLength A m k p : ℝ) : ℂ) *
          xiPhysicalApertureCharacterRate A n) *
        ((1 - Complex.exp (-(xiPhysicalPrimeLogApertureLength A m k p : ℂ) * r)) / r)) =
    Complex.exp (r * (e : ℂ)) - Complex.exp (r * (s : ℂ))
  rw [show xiPhysicalApertureCharacterRate A n = r by rfl,
    show xiPhysicalPrimeLogApertureStart m p = s by rfl,
    show xiPhysicalPrimeLogApertureLength A m k p = L by rfl]
  rw [hSL]
  field_simp [hr]
  rw [mul_comm (r : ℂ) (e : ℂ), mul_comm (r : ℂ) (s : ℂ),
    mul_comm (r : ℂ) (L : ℂ)]
  rw [mul_sub, mul_one, hexp]

/-- The endpoint measure's `n`th circle moment is the character rate times the physical packet
amplitude. -/
theorem sum_endpointCircleJump_mul_fourier
    {P : Finset Nat.Primes} {A m k : ℝ} (hA : 0 < A)
    {n : ℤ} (hn : n ≠ 0)
    (hactive : ∀ p ∈ P, 0 < xiPhysicalPrimeLogApertureLength A m k p) :
    ∑ x ∈ xiPhysicalPrimeLogEndpointNodeSet P A m k,
        xiPhysicalPrimeLogEndpointCircleJump P A m k x * fourier n x =
      xiPhysicalApertureCharacterRate A n *
        xiPhysicalPrimeLogCharacterAmplitude P A n m k := by
  rw [sum_endpointCircleJump_mul, xiPhysicalPrimeLogCharacterAmplitude]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← xiPhysicalApertureCharacterRate_mul_characterMoment hA hn p (hactive p hp)]
  ring

private theorem xiPhysicalPrimeLogEndpointCircleJump_eq_zero_of_not_mem
    {P : Finset Nat.Primes} {A m k : ℝ} {x : AddCircle A}
    (hx : x ∉ xiPhysicalPrimeLogEndpointNodeSet P A m k) :
    xiPhysicalPrimeLogEndpointCircleJump P A m k x = 0 := by
  classical
  rw [xiPhysicalPrimeLogEndpointCircleJump]
  have hend : xiPhysicalPrimeLogEndpointCircleEndWeight P A k x = 0 := by
    rw [xiPhysicalPrimeLogEndpointCircleEndWeight]
    apply Finset.sum_eq_zero
    intro p hp
    have hne : xiPhysicalPrimeLogEndpointNode A
        (xiPhysicalPrimeLogApertureEnd A k p) ≠ x := by
      intro heq
      exact hx (heq ▸ endpoint_node_mem_nodeSet_end (m := m) hp)
    simp [hne]
  have hstart : xiPhysicalPrimeLogEndpointCircleStartWeight P A m x = 0 := by
    rw [xiPhysicalPrimeLogEndpointCircleStartWeight]
    apply Finset.sum_eq_zero
    intro p hp
    have hne : xiPhysicalPrimeLogEndpointNode A
        (xiPhysicalPrimeLogApertureStart m p) ≠ x := by
      intro heq
      exact hx (heq ▸ endpoint_node_mem_nodeSet_start (k := k) hp)
    simp [hne]
  rw [hend, hstart, sub_zero]

private theorem endpointNode_mem_of_circleJump_ne_zero
    {P : Finset Nat.Primes} {A m k : ℝ} {x : AddCircle A}
    (hx : xiPhysicalPrimeLogEndpointCircleJump P A m k x ≠ 0) :
    x ∈ xiPhysicalPrimeLogEndpointNodeSet P A m k := by
  by_contra hmem
  exact hx (xiPhysicalPrimeLogEndpointCircleJump_eq_zero_of_not_mem hmem)

private theorem fourier_one_value_injective
    {A : ℝ} (hA : 0 < A) :
    Function.Injective (fun x : AddCircle A => fourier 1 x) := by
  intro x y hxy
  change fourier 1 x = fourier 1 y at hxy
  rw [fourier_one, fourier_one] at hxy
  apply AddCircle.injective_toCircle hA.ne'
  exact Subtype.ext hxy

private theorem fourier_one_pow
    {A : ℝ} (x : AddCircle A) (r : ℕ) :
    fourier 1 x ^ r = fourier (r : ℤ) x := by
  simp [fourier_apply, AddCircle.toCircle_nsmul]

private theorem fourier_one_ne_zero
    {A : ℝ} (x : AddCircle A) : fourier 1 x ≠ 0 := by
  intro hzero
  have hnorm : ‖fourier 1 x‖ = 1 := by simp
  rw [hzero, norm_zero] at hnorm
  norm_num at hnorm

/-- A nonempty active physical packet has a nonzero nonconstant character amplitude. The proof
uses the nonzero arithmetic endpoint jump and finite Vandermonde separation on the aperture
circle; no zero data or analytic estimate enters. -/
theorem exists_xiPhysicalPrimeLogCharacterAmplitude_ne_zero
    {P : Finset Nat.Primes} {A m k : ℝ}
    (hP : P.Nonempty)
    (hactive : ∀ p ∈ P, 0 < xiPhysicalPrimeLogApertureLength A m k p)
    (hwidth0 : 0 < k - m) (hwidthA : k - m < A) :
    ∃ n : ℤ, n ≠ 0 ∧
      xiPhysicalPrimeLogCharacterAmplitude P A n m k ≠ 0 := by
  classical
  have hA : 0 < A := hwidth0.trans hwidthA
  rcases exists_xiPhysicalPrimeLog_interiorEndpoint_nonzero_jump
      hP hactive hwidth0 hwidthA with ⟨t, ht0, htA, hjump⟩
  let x := xiPhysicalPrimeLogEndpointNode A t
  have hcircle : xiPhysicalPrimeLogEndpointCircleJump P A m k x ≠ 0 := by
    rw [xiPhysicalPrimeLogEndpointCircleJump_at_interior hA hactive ht0 htA]
    exact_mod_cast hjump
  let B := xiPhysicalPrimeLogEndpointNodeSet P A m k
  have hxB : x ∈ B := by
    exact endpointNode_mem_of_circleJump_ne_zero hcircle
  let b : B := ⟨x, hxB⟩
  let e := Fintype.equivFin B
  let μ : Fin (Fintype.card B) → ℂ := fun j => fourier 1 ((e.symm j : B) : AddCircle A)
  let c : Fin (Fintype.card B) → ℂ := fun j =>
    xiPhysicalPrimeLogEndpointCircleJump P A m k ((e.symm j : B) : AddCircle A) * μ j
  have hμ : Function.Injective μ := by
    intro i j hij
    apply e.symm.injective
    apply Subtype.ext
    apply fourier_one_value_injective hA
    simpa [μ] using hij
  have hc : c ≠ 0 := by
    intro hc0
    have hval := congrFun hc0 (e b)
    change xiPhysicalPrimeLogEndpointCircleJump P A m k
        ((e.symm (e b) : B) : AddCircle A) * μ (e b) = 0 at hval
    rw [e.symm_apply_apply] at hval
    have hbjump : xiPhysicalPrimeLogEndpointCircleJump P A m k
        (b : AddCircle A) ≠ 0 := by
      simpa [b] using hcircle
    have hbμ : μ (e b) ≠ 0 := by
      change fourier 1 ((e.symm (e b) : B) : AddCircle A) ≠ 0
      rw [e.symm_apply_apply]
      exact fourier_one_ne_zero (b : AddCircle A)
    exact (mul_ne_zero hbjump hbμ) hval
  rcases GaloisForLFunctions.vandermonde_initial_moment_nonzero_of_nonzero_coeff
      hμ hc with ⟨q, hq⟩
  let r : ℕ := (q : ℕ) + 1
  let n : ℤ := r
  have hn : n ≠ 0 := by
    change ((r : ℕ) : ℤ) ≠ 0
    exact Int.ofNat_ne_zero.mpr (by simp [r])
  have hq' : ∑ j, xiPhysicalPrimeLogEndpointCircleJump P A m k
        ((e.symm j : B) : AddCircle A) * μ j ^ r ≠ 0 := by
    have heq : (∑ j, c j * μ j ^ (q : ℕ)) =
        ∑ j, xiPhysicalPrimeLogEndpointCircleJump P A m k
          ((e.symm j : B) : AddCircle A) * μ j ^ r := by
      apply Fintype.sum_congr
      intro j
      change (xiPhysicalPrimeLogEndpointCircleJump P A m k
          ((e.symm j : B) : AddCircle A) * μ j) * μ j ^ (q : ℕ) =
        xiPhysicalPrimeLogEndpointCircleJump P A m k
          ((e.symm j : B) : AddCircle A) * μ j ^ ((q : ℕ) + 1)
      rw [pow_succ]
      ring
    intro hzero
    exact hq (heq.trans hzero)
  have hsubtype : ∑ y : B,
      xiPhysicalPrimeLogEndpointCircleJump P A m k (y : AddCircle A) *
        fourier 1 (y : AddCircle A) ^ r ≠ 0 := by
    have hreindex := e.symm.sum_comp (fun y : B =>
      xiPhysicalPrimeLogEndpointCircleJump P A m k (y : AddCircle A) *
        fourier 1 (y : AddCircle A) ^ r)
    intro hzero
    apply hq'
    simpa [μ] using hreindex.trans hzero
  have hfinset : ∑ y ∈ B,
      xiPhysicalPrimeLogEndpointCircleJump P A m k y * fourier 1 y ^ r ≠ 0 := by
    intro hzero
    apply hsubtype
    rw [← Finset.sum_attach] at hzero
    simpa using hzero
  have hfourier : ∑ y ∈ B,
      xiPhysicalPrimeLogEndpointCircleJump P A m k y * fourier n y ≠ 0 := by
    change ∑ y ∈ B,
      xiPhysicalPrimeLogEndpointCircleJump P A m k y * fourier (r : ℤ) y ≠ 0
    simpa only [fourier_one_pow] using hfinset
  have hproduct : xiPhysicalApertureCharacterRate A n *
      xiPhysicalPrimeLogCharacterAmplitude P A n m k ≠ 0 := by
    rw [← sum_endpointCircleJump_mul_fourier hA hn hactive]
    simpa [B] using hfourier
  exact ⟨n, hn, (mul_ne_zero_iff.mp hproduct).2⟩

/-- The complex coherent physical aperture carrier is nonzero for every nonempty active packet. -/
theorem xiPhysicalPrimeLogComplexAggregateApertureCarrier_ne_zero_of_nonempty_active
    {P : Finset Nat.Primes} {A m k : ℝ}
    (hP : P.Nonempty)
    (hactive : ∀ p ∈ P, 0 < xiPhysicalPrimeLogApertureLength A m k p)
    (hwidth0 : 0 < k - m) (hwidthA : k - m < A) :
    xiPhysicalPrimeLogComplexAggregateApertureCarrier P A m k ≠ 0 := by
  have hA : 0 < A := hwidth0.trans hwidthA
  rcases exists_xiPhysicalPrimeLogCharacterAmplitude_ne_zero
      hP hactive hwidth0 hwidthA with ⟨n, hn, hamp⟩
  intro hzero
  have hinner := inner_xiPhysicalPrimeLogComplexAggregate_character P hA hn m k
  rw [hzero, inner_zero_left] at hinner
  exact hamp hinner.symm

/-- `(PE9)`, nonzero direction: every nonempty active physical packet has nonzero real coherent
carrier. -/
theorem xiPhysicalPrimeLogAggregateApertureCarrier_ne_zero_of_nonempty_active
    {P : Finset Nat.Primes} {A m k : ℝ}
    (hP : P.Nonempty)
    (hactive : ∀ p ∈ P, 0 < xiPhysicalPrimeLogApertureLength A m k p)
    (hwidth0 : 0 < k - m) (hwidthA : k - m < A) :
    xiPhysicalPrimeLogAggregateApertureCarrier P A m k ≠ 0 := by
  have hA : 0 < A := hwidth0.trans hwidthA
  have hc :=
    xiPhysicalPrimeLogComplexAggregateApertureCarrier_ne_zero_of_nonempty_active
      hP hactive hwidth0 hwidthA
  intro hzero
  have hreal := xiPhysicalPrimeLogApertureFusionEnergy_eq_norm_sq P hA m k
  have hcomplex := xiPhysicalPrimeLogApertureFusionEnergy_eq_complex_norm_sq P hA m k
  rw [hzero, norm_zero, zero_pow (Nat.succ_ne_zero 1)] at hreal
  rw [hreal, eq_comm, sq_eq_zero_iff, norm_eq_zero] at hcomplex
  exact hc hcomplex

/-- Complete physical radical classification `(PE9)`: under the exact raw-width and activity
conditions, the coherent carrier vanishes exactly for the empty prime packet. -/
theorem xiPhysicalPrimeLogAggregateApertureCarrier_eq_zero_iff
    {P : Finset Nat.Primes} {A m k : ℝ}
    (hactive : ∀ p ∈ P, 0 < xiPhysicalPrimeLogApertureLength A m k p)
    (hwidth0 : 0 < k - m) (hwidthA : k - m < A) :
    xiPhysicalPrimeLogAggregateApertureCarrier P A m k = 0 ↔ P = ∅ := by
  constructor
  · intro hzero
    by_contra hP
    exact xiPhysicalPrimeLogAggregateApertureCarrier_ne_zero_of_nonempty_active
      (Finset.nonempty_iff_ne_empty.mpr hP) hactive hwidth0 hwidthA hzero
  · rintro rfl
    simp [xiPhysicalPrimeLogAggregateApertureCarrier]

/-- Strict source-specific fusion energy for every nonempty active packet. -/
theorem xiPhysicalPrimeLogApertureFusionEnergy_pos_of_nonempty_active
    {P : Finset Nat.Primes} {A m k : ℝ}
    (hP : P.Nonempty)
    (hactive : ∀ p ∈ P, 0 < xiPhysicalPrimeLogApertureLength A m k p)
    (hwidth0 : 0 < k - m) (hwidthA : k - m < A) :
    0 < xiPhysicalPrimeLogApertureFusionEnergy P A m k := by
  have hA : 0 < A := hwidth0.trans hwidthA
  rw [xiPhysicalPrimeLogApertureFusionEnergy_eq_norm_sq P hA m k]
  exact sq_pos_of_pos (norm_pos_iff.mpr
    (xiPhysicalPrimeLogAggregateApertureCarrier_ne_zero_of_nonempty_active
      hP hactive hwidth0 hwidthA))

/-- `(AH16)`: every nonempty active physical prime cloud has strictly positive normalized
aperture dispersion. -/
theorem xiPhysicalPrimeLogNormalizedApertureDispersion_pos_of_nonempty_active
    {P : Finset Nat.Primes} {A m k : ℝ}
    (hP : P.Nonempty)
    (hactive : ∀ p ∈ P, 0 < xiPhysicalPrimeLogApertureLength A m k p)
    (hwidth0 : 0 < k - m) (hwidthA : k - m < A) :
    0 < xiPhysicalPrimeLogNormalizedApertureDispersion P A m k := by
  have hA : 0 < A := hwidth0.trans hwidthA
  exact (xiPhysicalPrimeLogNormalizedApertureDispersion_pos_iff hP hA m k).2
    (xiPhysicalPrimeLogAggregateApertureCarrier_ne_zero_of_nonempty_active
      hP hactive hwidth0 hwidthA)

end

end RHTower
