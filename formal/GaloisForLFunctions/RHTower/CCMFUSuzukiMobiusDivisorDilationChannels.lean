import GaloisForLFunctions.RHTower.CCMFUSuzukiMobiusDivisorAbelProducer
import GaloisForLFunctions.HTGeometry.DiscreteAbelRing

/-!
# Dilation-channel decomposition of the CCM-FU Möbius--divisor producer

The prime-free producer is not a collection of independent estimates.  Before scalarization it is
a triangular array indexed by Abel time `k` and Möbius dilation `d ≤ k`.  This module transposes
that literal finite array without taking absolute values.  The result isolates the actual
source-faithful dilation channels whose *joint signed cofinal sum* is RH-bearing.

No convergence premise, RH assumption, positivity replacement, or computation is used.
-/

open Filter Topology

noncomputable section

namespace RHTower

open ArithmeticFunction Finset

/-- Exact telescoping of the half-order Abel kernel on an arbitrary nonempty integer interval. -/
theorem sum_sqrt_succ_sub_sqrt_Icc_general
    {a b : ℕ} (hab : a ≤ b) :
    (∑ k ∈ Finset.Icc a b,
      (Real.sqrt (k + 1 : ℕ) - Real.sqrt k)) =
      Real.sqrt (b + 1 : ℕ) - Real.sqrt a := by
  rw [← Finset.Ico_add_one_right_eq_Icc]
  change (∑ k ∈ Finset.Ico a b.succ,
      (Real.sqrt k.succ - Real.sqrt k)) =
    Real.sqrt b.succ - Real.sqrt a
  rw [Finset.sum_Ico_eq_sub _ (Nat.le_succ_of_le hab)]
  simp_rw [Finset.sum_range_sub (fun i : ℕ => Real.sqrt i)]
  ring

/-- A floor-dilation fibre is one literal clipped quotient block. -/
theorem filter_Icc_div_eq_block
    {M d q : ℕ} (hd : 1 ≤ d) (hq : 1 ≤ q) :
    (Finset.Icc d (M - 1)).filter (fun k => k / d = q) =
      Finset.Icc (q * d) (min (M - 1) ((q + 1) * d - 1)) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hdk, hkM⟩, hkdiv⟩
    have hlower : q * d ≤ k := by
      rw [← hkdiv]
      exact Nat.div_mul_le_self k d
    have hupperlt : k < (q + 1) * d := by
      rw [← Nat.div_lt_iff_lt_mul (by omega : 0 < d)]
      omega
    exact ⟨hlower, le_min hkM (by omega)⟩
  · rintro ⟨hlower, hupper⟩
    have hkM : k ≤ M - 1 := hupper.trans (min_le_left _ _)
    have hupperlt : k < (q + 1) * d := by
      have := hupper.trans (min_le_right _ _)
      have hpos : 0 < (q + 1) * d := Nat.mul_pos (by omega) (by omega)
      omega
    have hkdiv : k / d = q :=
      Nat.div_eq_of_lt_le hlower hupperlt
    have hdk : d ≤ k := by
      exact (Nat.le_mul_of_pos_left d hq).trans hlower
    exact ⟨⟨hdk, hkM⟩, hkdiv⟩

/-- **Exact clipped-block Abel law.**  On one quotient fibre the divisor defect is constant, so
the complete half-order Abel weight telescopes to the difference of the two physical square-root
endpoints.  The last block is clipped at `M`; no asymptotic boundary term is discarded. -/
theorem sum_divisorDilationQuotientBlock
    {M d q : ℕ} (hd : 1 ≤ d) (hq : 1 ≤ q)
    (hqM : q ≤ (M - 1) / d) :
    (∑ k ∈ (Finset.Icc d (M - 1)).filter (fun k => k / d = q),
      (Real.sqrt (k + 1 : ℕ) - Real.sqrt k) *
        primeFreeDivisorDefect (k / d)) =
      (Real.sqrt (min (M - 1) ((q + 1) * d - 1) + 1 : ℕ) -
          Real.sqrt (q * d : ℕ)) * primeFreeDivisorDefect q := by
  let S := (Finset.Icc d (M - 1)).filter (fun k => k / d = q)
  calc
    (∑ k ∈ S, (Real.sqrt (k + 1 : ℕ) - Real.sqrt k) *
        primeFreeDivisorDefect (k / d)) =
      ∑ k ∈ S, (Real.sqrt (k + 1 : ℕ) - Real.sqrt k) *
        primeFreeDivisorDefect q := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkdiv : k / d = q := (Finset.mem_filter.mp hk).2
      rw [hkdiv]
    _ = (∑ k ∈ S, (Real.sqrt (k + 1 : ℕ) - Real.sqrt k)) *
        primeFreeDivisorDefect q := by rw [Finset.sum_mul]
    _ = (Real.sqrt (min (M - 1) ((q + 1) * d - 1) + 1 : ℕ) -
          Real.sqrt (q * d : ℕ)) * primeFreeDivisorDefect q := by
      have hlowerM : q * d ≤ M - 1 :=
        (Nat.le_div_iff_mul_le (by omega : 0 < d)).mp hqM
      have hlowerNext : q * d ≤ (q + 1) * d - 1 := by
        have hlt : q * d < (q + 1) * d := by
          exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
        omega
      have hab : q * d ≤ min (M - 1) ((q + 1) * d - 1) :=
        le_min hlowerM hlowerNext
      rw [show S = Finset.Icc (q * d)
          (min (M - 1) ((q + 1) * d - 1)) by
        exact filter_Icc_div_eq_block hd hq]
      rw [sum_sqrt_succ_sub_sqrt_Icc_general hab]

/-- Exact square-root mass of a clipped floor-dilation quotient block. -/
def divisorDilationClippedAbelWeight (M d q : ℕ) : ℝ :=
  Real.sqrt (min (M - 1) ((q + 1) * d - 1) + 1 : ℕ) -
    Real.sqrt (q * d : ℕ)

/-- A complete quotient block separates exactly into dilation and Abel square-root factors. -/
theorem divisorDilationClippedAbelWeight_eq_full
    {M d q : ℕ} (hd : 1 ≤ d) (hq : 1 ≤ q)
    (hfull : (q + 1) * d ≤ M) :
    divisorDilationClippedAbelWeight M d q =
      Real.sqrt d * (Real.sqrt (q + 1 : ℕ) - Real.sqrt q) := by
  rw [divisorDilationClippedAbelWeight]
  have hprod : 1 ≤ (q + 1) * d := Nat.mul_pos (by omega) (by omega)
  have hmin : min (M - 1) ((q + 1) * d - 1) = (q + 1) * d - 1 :=
    min_eq_right (by omega)
  rw [hmin, Nat.sub_add_cancel hprod]
  push_cast
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ q + 1),
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ q)]
  ring

/-- The unique incomplete quotient block retains the literal moving endpoint `sqrt M`. -/
theorem divisorDilationClippedAbelWeight_eq_terminal
    {M d q : ℕ} (hd : 1 ≤ d) (hq : 1 ≤ q)
    (hqd : q * d ≤ M - 1)
    (hterminal : M < (q + 1) * d) :
    divisorDilationClippedAbelWeight M d q =
      Real.sqrt M - Real.sqrt (q * d : ℕ) := by
  rw [divisorDilationClippedAbelWeight]
  have hmin : min (M - 1) ((q + 1) * d - 1) = M - 1 :=
    min_eq_left (by omega)
  have hqdpos : 0 < q * d := Nat.mul_pos (by omega) (by omega)
  have hM : 1 ≤ M := by omega
  rw [hmin, Nat.sub_add_cancel hM]

/-- Integer length of the physical clipped block: `min (M - q*d) d`. -/
def divisorDilationTriangularLength (M d q : ℕ) : ℕ :=
  min (M - q * d) d

/-- **Rationalized dilation-tent law.**  Every physical kernel coefficient is its literal clipped
integer block length divided by the sum of its square-root endpoints.  Hence the moving kernel is
positive before the Möbius sign is applied, and prime--polar cancellation is localized entirely in
the signed dilation aggregation. -/
theorem divisorDilationClippedAbelWeight_eq_triangular
    {M d q : ℕ} (hd : 1 ≤ d) (hq : 1 ≤ q)
    (hqd : q * d ≤ M - 1) :
    divisorDilationClippedAbelWeight M d q =
      (divisorDilationTriangularLength M d q : ℝ) /
        (Real.sqrt (min M ((q + 1) * d) : ℕ) +
          Real.sqrt (q * d : ℕ)) := by
  have hqdpos : 0 < q * d := Nat.mul_pos (by omega) (by omega)
  have hM : 1 ≤ M := by omega
  have hX : 1 ≤ (q + 1) * d := Nat.mul_pos (by omega) (by omega)
  have hendpoint :
      min (M - 1) ((q + 1) * d - 1) + 1 = min M ((q + 1) * d) := by
    by_cases hMX : M ≤ (q + 1) * d
    · rw [min_eq_left (by omega), min_eq_left hMX,
        Nat.sub_add_cancel hM]
    · have hXM : (q + 1) * d ≤ M := by omega
      rw [min_eq_right (by omega), min_eq_right hXM,
        Nat.sub_add_cancel hX]
  have hprod : (q + 1) * d = q * d + d := by ring
  have hlength :
      min M ((q + 1) * d) - q * d =
        divisorDilationTriangularLength M d q := by
    rw [divisorDilationTriangularLength, hprod]
    by_cases hMsum : M ≤ q * d + d
    · rw [min_eq_left hMsum, min_eq_left]
      omega
    · have hsumM : q * d + d ≤ M := by omega
      have hdsub : d ≤ M - q * d := by omega
      rw [min_eq_right hsumM, min_eq_right hdsub]
      omega
  have hqmin : q * d ≤ min M ((q + 1) * d) := by
    apply le_min
    · omega
    · rw [hprod]
      omega
  have hden :
      Real.sqrt (min M ((q + 1) * d) : ℕ) + Real.sqrt (q * d : ℕ) ≠ 0 := by
    positivity
  rw [divisorDilationClippedAbelWeight, hendpoint]
  apply (eq_div_iff hden).2
  have hsqA : Real.sqrt (min M ((q + 1) * d) : ℕ) ^ 2 =
      (min M ((q + 1) * d) : ℕ) :=
    Real.sq_sqrt (by positivity)
  have hsqB : Real.sqrt (q * d : ℕ) ^ 2 = (q * d : ℕ) :=
    Real.sq_sqrt (by positivity)
  have hcast :
      (divisorDilationTriangularLength M d q : ℝ) =
        ((min M ((q + 1) * d) : ℕ) : ℝ) - ((q * d : ℕ) : ℝ) := by
    rw [← hlength, Nat.cast_sub hqmin]
  nlinarith

/-- Every coefficient in the physical dilation tent is strictly positive on its support. -/
theorem divisorDilationClippedAbelWeight_pos
    {M d q : ℕ} (hd : 1 ≤ d) (hq : 1 ≤ q)
    (hqd : q * d ≤ M - 1) :
    0 < divisorDilationClippedAbelWeight M d q := by
  rw [divisorDilationClippedAbelWeight_eq_triangular hd hq hqd]
  apply div_pos
  · exact_mod_cast (show 0 < divisorDilationTriangularLength M d q by
      rw [divisorDilationTriangularLength]
      exact lt_min (by
        have hqdpos : 0 < q * d := Nat.mul_pos (by omega) (by omega)
        omega) (by omega))
  · have hqdpos : 0 < q * d := Nat.mul_pos (by omega) (by omega)
    exact add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _)
      (Real.sqrt_pos.mpr (by exact_mod_cast hqdpos))

/-- One literal Möbius dilation channel of the prime-free half-order Abel producer.  Its Möbius
sign remains outside the complete time channel and the divisor defect retains the exact floor
argument `k / d`. -/
def mobiusDivisorDilationChannel (M d : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
    ∑ k ∈ Finset.Icc d (M - 1),
      (Real.sqrt (k + 1 : ℕ) - Real.sqrt k) *
        primeFreeDivisorDefect (k / d)

/-- **Clipped quotient-block factorization.**  Every dilation channel is exactly its Möbius sign
times a sum of prime-free divisor defects against the physical square-root mass of each complete
or terminally clipped quotient block.  This removes the redundant time coordinate while retaining
the moving boundary coefficient exactly. -/
theorem mobiusDivisorDilationChannel_eq_quotientBlocks
    {M d : ℕ} (hd : 1 ≤ d) :
    mobiusDivisorDilationChannel M d =
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        ∑ q ∈ Finset.Icc 1 ((M - 1) / d),
          divisorDilationClippedAbelWeight M d q *
            primeFreeDivisorDefect q := by
  rw [mobiusDivisorDilationChannel]
  let K := Finset.Icc d (M - 1)
  let Q := Finset.Icc 1 ((M - 1) / d)
  congr 1
  calc
    (∑ k ∈ K, (Real.sqrt (k + 1 : ℕ) - Real.sqrt k) *
        primeFreeDivisorDefect (k / d)) =
      ∑ k ∈ K, ∑ q ∈ Q,
        if k / d = q then
          (Real.sqrt (k + 1 : ℕ) - Real.sqrt k) *
            primeFreeDivisorDefect (k / d)
        else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k ∈ Finset.Icc d (M - 1) := by simpa only [K] using hk
      have hqmem : k / d ∈ Q := by
        simp only [Q, Finset.mem_Icc]
        constructor
        · exact (Nat.le_div_iff_mul_le (by omega : 0 < d)).2
            (by simpa using (Finset.mem_Icc.mp hk').1)
        · exact Nat.div_le_div_right (Finset.mem_Icc.mp hk').2
      have hflip :
          (∑ q ∈ Q, if k / d = q then
              (Real.sqrt (k + 1 : ℕ) - Real.sqrt k) *
                primeFreeDivisorDefect (k / d)
            else 0) =
            ∑ q ∈ Q, if q = k / d then
              (Real.sqrt (k + 1 : ℕ) - Real.sqrt k) *
                primeFreeDivisorDefect (k / d)
            else 0 := by
        apply Finset.sum_congr rfl
        intro q hq
        by_cases heq : q = k / d
        · subst q
          rfl
        · rw [if_neg heq, if_neg (Ne.symm heq)]
      rw [hflip, Finset.sum_ite_eq' Q (k / d), if_pos hqmem]
    _ = ∑ q ∈ Q, ∑ k ∈ K,
        if k / d = q then
          (Real.sqrt (k + 1 : ℕ) - Real.sqrt k) *
            primeFreeDivisorDefect (k / d)
        else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ q ∈ Q, ∑ k ∈ K.filter (fun k => k / d = q),
          (Real.sqrt (k + 1 : ℕ) - Real.sqrt k) *
            primeFreeDivisorDefect (k / d) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.sum_filter]
    _ = ∑ q ∈ Q,
        divisorDilationClippedAbelWeight M d q *
          primeFreeDivisorDefect q := by
      apply Finset.sum_congr rfl
      intro q hq
      have hq' := Finset.mem_Icc.mp (by simpa only [Q] using hq)
      rw [sum_divisorDilationQuotientBlock hd hq'.1 hq'.2]
      rfl

/-- Finite hyperbola Fubini law.  The two orders enumerate the same pairs `d*q ≤ N`. -/
theorem sum_hyperbola_swap_real (N : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ d ∈ Finset.Icc 1 N, ∑ q ∈ Finset.Icc 1 (N / d), F d q) =
      ∑ q ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 (N / q), F d q := by
  let K := Finset.Icc 1 N
  have hfiber : ∀ d ∈ K,
      Finset.Icc 1 (N / d) = K.filter (fun q => d * q ≤ N) := by
    intro d hd
    have hd' := Finset.mem_Icc.mp (by simpa only [K] using hd)
    ext q
    simp only [Finset.mem_Icc, Finset.mem_filter, K]
    constructor
    · intro hq
      have hdpos : 0 < d := by omega
      exact ⟨⟨hq.1, hq.2.trans (Nat.div_le_self N d)⟩,
        (by simpa [Nat.mul_comm] using
          (Nat.le_div_iff_mul_le hdpos).mp hq.2)⟩
    · intro hq
      exact ⟨hq.1.1,
        (Nat.le_div_iff_mul_le (by omega : 0 < d)).2
          (by simpa [Nat.mul_comm] using hq.2)⟩
  rw [show Finset.Icc 1 N = K by rfl]
  calc
    (∑ d ∈ K, ∑ q ∈ Finset.Icc 1 (N / d), F d q) =
        ∑ d ∈ K, ∑ q ∈ K, if d * q ≤ N then F d q else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [hfiber d hd, Finset.sum_filter]
    _ = ∑ q ∈ K, ∑ d ∈ K, if d * q ≤ N then F d q else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ q ∈ K, ∑ d ∈ Finset.Icc 1 (N / q), F d q := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [hfiber q hq, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hmul : d * q ≤ N
      · rw [if_pos hmul, if_pos (by simpa [Nat.mul_comm] using hmul)]
      · rw [if_neg hmul, if_neg (by simpa [Nat.mul_comm] using hmul)]

/-- Möbius aggregation of all clipped dilation weights landing on divisor-defect cell `q`. -/
def mobiusClippedAbelKernel (M q : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 ((M - 1) / q),
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
      divisorDilationClippedAbelWeight M d q

/-- Zero-extended physical dilation tent.  Extension by zero is part of the source: it makes the
escaped upper coefficient vanish exactly instead of leaving an artificial Abel boundary debt. -/
def mobiusDilationTentWeight (M q d : ℕ) : ℝ :=
  if 1 ≤ d ∧ q * d ≤ M - 1 then
    divisorDilationClippedAbelWeight M d q
  else 0

/-- The collapsed kernel is the signed Möbius readout of the zero-extended physical tent. -/
theorem mobiusClippedAbelKernel_eq_tentSum
    {M q : ℕ} (hq : 1 ≤ q) :
    mobiusClippedAbelKernel M q =
      ∑ d ∈ Finset.Icc 1 ((M - 1) / q),
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
          mobiusDilationTentWeight M q d := by
  rw [mobiusClippedAbelKernel]
  apply Finset.sum_congr rfl
  intro d hd
  have hdI := Finset.mem_Icc.mp hd
  have hqd : q * d ≤ M - 1 := by
    simpa [Nat.mul_comm] using
      (Nat.le_div_iff_mul_le (by omega : 0 < q)).mp hdI.2
  rw [mobiusDilationTentWeight, if_pos ⟨hdI.1, hqd⟩]

/-- The coefficient immediately beyond the physical dilation support vanishes exactly. -/
theorem mobiusDilationTentWeight_boundary_zero
    {M q : ℕ} (hq : 1 ≤ q) :
    mobiusDilationTentWeight M q (((M - 1) / q) + 1) = 0 := by
  rw [mobiusDilationTentWeight, if_neg]
  intro h
  have hlt : M - 1 < (((M - 1) / q) + 1) * q := by
    rw [← Nat.div_lt_iff_lt_mul (by omega : 0 < q)]
    omega
  have : q * (((M - 1) / q) + 1) ≤ M - 1 := h.2
  rw [Nat.mul_comm] at this
  omega

/-- **Boundary-free Mertens-gradient law.**  Exact Abel summation moves the Möbius signs onto their
literal partial sums and differentiates the positive dilation tent.  Zero extension cancels the
outer Abel coefficient identically, so no `|d|²`-type boundary debt remains.  Positive and negative
gradient regions stay coupled in the same finite sum. -/
theorem mobiusClippedAbelKernel_eq_mertensGradient
    {M q : ℕ} (hq : 1 ≤ q) :
    mobiusClippedAbelKernel M q =
      ∑ d ∈ Finset.Icc 1 ((M - 1) / q),
        (∑ k ∈ Finset.Icc 1 d,
          ((ArithmeticFunction.moebius k : ℤ) : ℝ)) *
        (mobiusDilationTentWeight M q d -
          mobiusDilationTentWeight M q (d + 1)) := by
  rw [mobiusClippedAbelKernel_eq_tentSum hq]
  have habel := HTGeometry.sum_mul_eq_partial_mul_diff_ring
    (fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ))
    (mobiusDilationTentWeight M q) ((M - 1) / q)
  rw [habel, mobiusDilationTentWeight_boundary_zero hq, mul_zero, add_zero]

/-- On complete blocks the tent rises strictly, so its Abel gradient is negative. -/
theorem mobiusDilationTentWeight_sub_succ_neg_of_full
    {M q d : ℕ} (hq : 1 ≤ q) (hd : 1 ≤ d)
    (hfull : (q + 1) * (d + 1) ≤ M) :
    mobiusDilationTentWeight M q d -
        mobiusDilationTentWeight M q (d + 1) < 0 := by
  have hqdsucc : q * (d + 1) ≤ M - 1 := by
    have hlt : q * (d + 1) < (q + 1) * (d + 1) :=
      Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    omega
  have hqd : q * d ≤ M - 1 := by
    exact (Nat.mul_le_mul_left q (by omega : d ≤ d + 1)).trans hqdsucc
  have hfullD : (q + 1) * d ≤ M :=
    (Nat.mul_le_mul_left (q + 1) (by omega : d ≤ d + 1)).trans hfull
  rw [mobiusDilationTentWeight, if_pos ⟨hd, hqd⟩,
    mobiusDilationTentWeight, if_pos ⟨by omega, hqdsucc⟩,
    divisorDilationClippedAbelWeight_eq_full hd hq hfullD,
    divisorDilationClippedAbelWeight_eq_full (by omega) hq hfull]
  have hc : 0 < Real.sqrt (q + 1 : ℕ) - Real.sqrt q := by
    have hcast : (q : ℝ) < ((q + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.lt_succ_self q)
    have := Real.sqrt_lt_sqrt (by positivity : (0 : ℝ) ≤ q) hcast
    linarith
  have hdcast : (d : ℝ) < ((d + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.lt_succ_self d)
  have hdroot : Real.sqrt d < Real.sqrt (d + 1 : ℕ) :=
    Real.sqrt_lt_sqrt (by positivity) hdcast
  nlinarith

/-- Inside the clipped terminal band the tent falls strictly, so its Abel gradient is positive. -/
theorem mobiusDilationTentWeight_sub_succ_pos_of_terminal
    {M q d : ℕ} (hq : 1 ≤ q) (hd : 1 ≤ d)
    (hqdsucc : q * (d + 1) ≤ M - 1)
    (hterminal : M < (q + 1) * d) :
    0 < mobiusDilationTentWeight M q d -
        mobiusDilationTentWeight M q (d + 1) := by
  have hqd : q * d ≤ M - 1 := by
    exact (Nat.mul_le_mul_left q (by omega : d ≤ d + 1)).trans hqdsucc
  have hterminalSucc : M < (q + 1) * (d + 1) :=
    hterminal.trans_le (Nat.mul_le_mul_left (q + 1) (by omega))
  rw [mobiusDilationTentWeight, if_pos ⟨hd, hqd⟩,
    mobiusDilationTentWeight, if_pos ⟨by omega, hqdsucc⟩,
    divisorDilationClippedAbelWeight_eq_terminal hd hq hqd hterminal,
    divisorDilationClippedAbelWeight_eq_terminal (by omega) hq hqdsucc hterminalSucc]
  have hroot : Real.sqrt (q * d : ℕ) < Real.sqrt (q * (d + 1) : ℕ) := by
    apply Real.sqrt_lt_sqrt (by positivity)
    exact_mod_cast Nat.mul_lt_mul_of_pos_left (by omega : d < d + 1) (by omega : 0 < q)
  linarith

/-- Last physical edge has a strictly positive gradient because the escaped coefficient is zero. -/
theorem mobiusDilationTentWeight_lastGradient_pos
    {M q : ℕ} (hq : 1 ≤ q) (hqM : q ≤ M - 1) :
    0 < mobiusDilationTentWeight M q ((M - 1) / q) -
        mobiusDilationTentWeight M q (((M - 1) / q) + 1) := by
  let d := (M - 1) / q
  have hd : 1 ≤ d := by
    dsimp [d]
    exact (Nat.le_div_iff_mul_le (by omega : 0 < q)).2 (by simpa using hqM)
  have hqd : q * d ≤ M - 1 := by
    dsimp [d]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (M - 1) q
  rw [mobiusDilationTentWeight_boundary_zero hq, sub_zero]
  rw [mobiusDilationTentWeight, if_pos ⟨hd, hqd⟩]
  exact divisorDilationClippedAbelWeight_pos hd hq hqd

/-- Square-root-weighted Mertens sum generated by complete quotient blocks. -/
def weightedMobiusSquareRootSum (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N,
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.sqrt d

/-- Moving-boundary remainder supported on the terminal dilation band. -/
def mobiusTerminalClippedAbelKernel (M q : ℕ) : ℝ :=
  ∑ d ∈ Finset.Ioc (M / (q + 1)) ((M - 1) / q),
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
      (Real.sqrt M - Real.sqrt (q * d : ℕ))

/-- **Exact complete/terminal boundary split.**  The collapsed kernel is a half-order Abel factor
times a square-root-weighted Mertens sum, plus one literal terminal-band correction.  This is the
coefficient-faithful boundary transport law: discarding the terminal term would change the source,
while estimating the two terms separately would destroy their possible cancellation. -/
theorem mobiusClippedAbelKernel_eq_full_add_terminal
    {M q : ℕ} (hq : 1 ≤ q) :
    mobiusClippedAbelKernel M q =
      (Real.sqrt (q + 1 : ℕ) - Real.sqrt q) *
          weightedMobiusSquareRootSum (M / (q + 1)) +
        mobiusTerminalClippedAbelKernel M q := by
  let A := M / (q + 1)
  let B := (M - 1) / q
  have hAB : A ≤ B := by
    by_cases hA0 : A = 0
    · simp [hA0]
    · have hApos : 0 < A := Nat.pos_of_ne_zero hA0
      have hprod : (q + 1) * A ≤ M := by
        dsimp [A]
        simpa [Nat.mul_comm] using Nat.div_mul_le_self M (q + 1)
      have hqA : q * A ≤ M - 1 := by
        have hlt : q * A < (q + 1) * A := by
          nlinarith
        omega
      exact (Nat.le_div_iff_mul_le (by omega : 0 < q)).2
        (by simpa [Nat.mul_comm] using hqA)
  have hsplit : Finset.Icc 1 B =
      Finset.Icc 1 A ∪ Finset.Ioc A B := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    constructor
    · intro hdB
      by_cases hdA : d ≤ A
      · exact Or.inl ⟨hdB.1, hdA⟩
      · exact Or.inr ⟨lt_of_not_ge hdA, hdB.2⟩
    · intro hd
      rcases hd with hd | hd
      · exact ⟨hd.1, hd.2.trans hAB⟩
      · exact ⟨Nat.one_le_iff_ne_zero.mpr
          ((Nat.zero_le A).trans_lt hd.1).ne', hd.2⟩
  have hdisj : Disjoint (Finset.Icc 1 A) (Finset.Ioc A B) := by
    rw [Finset.disjoint_left]
    intro d hdA hdB
    simp only [Finset.mem_Icc] at hdA
    simp only [Finset.mem_Ioc] at hdB
    omega
  rw [mobiusClippedAbelKernel]
  change (∑ d ∈ Finset.Icc 1 B,
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        divisorDilationClippedAbelWeight M d q) = _
  rw [hsplit, Finset.sum_union hdisj]
  rw [weightedMobiusSquareRootSum, mobiusTerminalClippedAbelKernel]
  change
    (∑ d ∈ Finset.Icc 1 A,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
          divisorDilationClippedAbelWeight M d q) +
      (∑ d ∈ Finset.Ioc A B,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
          divisorDilationClippedAbelWeight M d q) =
      (Real.sqrt (q + 1 : ℕ) - Real.sqrt q) *
        ∑ d ∈ Finset.Icc 1 A,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.sqrt d +
      ∑ d ∈ Finset.Ioc A B,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
          (Real.sqrt M - Real.sqrt (q * d : ℕ))
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hdmem
    have hdI := Finset.mem_Icc.mp hdmem
    have hfull : (q + 1) * d ≤ M := by
      simpa [Nat.mul_comm] using
        (Nat.le_div_iff_mul_le (by omega : 0 < q + 1)).mp hdI.2
    rw [divisorDilationClippedAbelWeight_eq_full hdI.1 hq hfull]
    ring
  · apply Finset.sum_congr rfl
    intro d hdmem
    have hdI := Finset.mem_Ioc.mp hdmem
    have hqd : q * d ≤ M - 1 := by
      simpa [Nat.mul_comm] using
        (Nat.le_div_iff_mul_le (by omega : 0 < q)).mp hdI.2
    have hterminal : M < (q + 1) * d := by
      have := Nat.lt_mul_of_div_lt hdI.1 (by omega : 0 < q + 1)
      simpa [Nat.mul_comm] using this
    have hdpos : 0 < d := (Nat.zero_le A).trans_lt hdI.1
    rw [divisorDilationClippedAbelWeight_eq_terminal
      (Nat.one_le_iff_ne_zero.mpr hdpos.ne') hq hqd hterminal]

/-- **Coefficient-faithful dilation-channel law.**  The pre-scalar Möbius--divisor producer is
exactly the signed cofinal sum of its dilation channels.  This is a finite Fubini theorem on the
literal triangular source `1 ≤ d ≤ k < M`; no sign, floor label, or Abel coefficient is changed. -/
theorem mobiusDivisorSquareRootAbelMoment_eq_sum_dilationChannels
    (M : ℕ) :
    mobiusDivisorSquareRootAbelMoment M =
      ∑ d ∈ Finset.Icc 1 (M - 1), mobiusDivisorDilationChannel M d := by
  rw [mobiusDivisorSquareRootAbelMoment]
  let K := Finset.Icc 1 (M - 1)
  have hinner : ∀ k ∈ K,
      (∑ d ∈ Finset.Icc 1 k,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
            primeFreeDivisorDefect (k / d)) =
        ∑ d ∈ K,
          if d ≤ k then
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
              primeFreeDivisorDefect (k / d)
          else 0 := by
    intro k hk
    have hk' : k ∈ Finset.Icc 1 (M - 1) := by
      simpa only [K] using hk
    have hset : Finset.Icc 1 k = K.filter (fun d => d ≤ k) := by
      ext d
      simp only [Finset.mem_Icc, Finset.mem_filter, K]
      constructor
      · intro hd
        exact ⟨⟨hd.1, hd.2.trans (Finset.mem_Icc.mp hk').2⟩, hd.2⟩
      · intro hd
        exact ⟨hd.1.1, hd.2⟩
    rw [hset, Finset.sum_filter]
  rw [show Finset.Icc 1 (M - 1) = K by rfl]
  calc
    (∑ k ∈ K,
        (Real.sqrt (k + 1 : ℕ) - Real.sqrt k) *
          ∑ d ∈ Finset.Icc 1 k,
            ↑(ArithmeticFunction.moebius d) * primeFreeDivisorDefect (k / d)) =
        ∑ k ∈ K,
          (Real.sqrt (k + 1 : ℕ) - Real.sqrt k) *
            ∑ d ∈ K, if d ≤ k then
              ↑(ArithmeticFunction.moebius d) * primeFreeDivisorDefect (k / d)
            else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hinner k hk]
    _ = ∑ k ∈ K, ∑ d ∈ K,
          if d ≤ k then
            ↑(ArithmeticFunction.moebius d) *
              ((Real.sqrt (k + 1 : ℕ) - Real.sqrt k) *
                primeFreeDivisorDefect (k / d))
          else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      split_ifs <;> ring
    _ = ∑ d ∈ K, ∑ k ∈ K,
          if d ≤ k then
            ↑(ArithmeticFunction.moebius d) *
              ((Real.sqrt (k + 1 : ℕ) - Real.sqrt k) *
                primeFreeDivisorDefect (k / d))
          else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ d ∈ K, mobiusDivisorDilationChannel M d := by
      apply Finset.sum_congr rfl
      intro d hd
      have hd' : d ∈ Finset.Icc 1 (M - 1) := by
        simpa only [K] using hd
      rw [mobiusDivisorDilationChannel]
      have hset : K.filter (fun k => d ≤ k) = Finset.Icc d (M - 1) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_Icc, K]
        constructor
        · intro hk
          exact ⟨hk.2, hk.1.2⟩
        · intro hk
          exact ⟨⟨(Finset.mem_Icc.mp hd').1.trans hk.1, hk.2⟩, hk.1⟩
      rw [← hset, Finset.mul_sum, Finset.sum_filter]

/-- **Collapsed Möbius-kernel producer.**  The complete source is the prime-free divisor defect
paired with one explicit moving kernel.  Each kernel coefficient is the signed Möbius aggregation
of the exact clipped square-root block masses.  Thus no von Mangoldt coefficient remains and the
only possible cofinal gain is joint cancellation inside `mobiusClippedAbelKernel`; separate
dilation-channel estimates cannot create it. -/
theorem mobiusDivisorSquareRootAbelMoment_eq_divisorDefect_kernel
    (M : ℕ) :
    mobiusDivisorSquareRootAbelMoment M =
      ∑ q ∈ Finset.Icc 1 (M - 1),
        primeFreeDivisorDefect q * mobiusClippedAbelKernel M q := by
  rw [mobiusDivisorSquareRootAbelMoment_eq_sum_dilationChannels]
  have hchannels :
      (∑ d ∈ Finset.Icc 1 (M - 1), mobiusDivisorDilationChannel M d) =
        ∑ d ∈ Finset.Icc 1 (M - 1),
          ∑ q ∈ Finset.Icc 1 ((M - 1) / d),
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
              divisorDilationClippedAbelWeight M d q *
                primeFreeDivisorDefect q := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [mobiusDivisorDilationChannel_eq_quotientBlocks
      (Finset.mem_Icc.mp hd).1, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    ring
  rw [hchannels, sum_hyperbola_swap_real]
  apply Finset.sum_congr rfl
  intro q hq
  rw [mobiusClippedAbelKernel, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  ring

end RHTower
