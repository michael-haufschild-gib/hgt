import GaloisForLFunctions.HTGeometry.IncompleteTensorProduct
import GaloisForLFunctions.RHTower.WoldThermofieldSectorFracture

open scoped BigOperators ENNReal InnerProductSpace
open Filter Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Literal one-prime standard-form Hilbert factor `ℓ²(ℕ₀ × ℕ₀)`. -/
abbrev PrimeThermofieldLocalHilbert (_p : Nat.Primes) : Type :=
  lp (fun _ : ℕ × ℕ => ℂ) 2

theorem primeRadialCriticalMass_nonneg (p : Nat.Primes) :
    0 ≤ primeRadialCriticalMass p :=
  inv_nonneg.mpr (by exact_mod_cast p.2.pos.le)

theorem primeRadialCriticalMass_lt_one (p : Nat.Primes) :
    primeRadialCriticalMass p < 1 := by
  exact (inv_lt_one₀ (by exact_mod_cast p.2.pos)).2
    (by exact_mod_cast p.2.one_lt)

/-- One-prime critical occupation half-density. -/
def primeCriticalLocalHalfDensity (p : Nat.Primes) :
    lp (fun _ : ℕ => ℂ) 2 :=
  geometricOccupationHalfDensity (primeRadialCriticalMass p)
    (primeRadialCriticalMass_nonneg p) (primeRadialCriticalMass_lt_one p)

/-- Diagonal standard-form lift of the one-prime critical Wold state. -/
def primeCriticalLocalThermofieldVector (p : Nat.Primes) :
    PrimeThermofieldLocalHilbert p :=
  ⟨thermofieldDiagonalKernel (primeCriticalLocalHalfDensity p),
    (thermofieldDiagonalKernel_isHS (primeCriticalLocalHalfDensity p)).memℓp⟩

theorem norm_primeCriticalLocalThermofieldVector (p : Nat.Primes) :
    ‖primeCriticalLocalThermofieldVector p‖ = 1 := by
  have hsq : ‖primeCriticalLocalThermofieldVector p‖ ^ 2 = 1 := by
    calc
      ‖primeCriticalLocalThermofieldVector p‖ ^ 2 =
          HilbertSchmidt.hsNormSq
            (thermofieldDiagonalKernel (primeCriticalLocalHalfDensity p)) :=
        HilbertSchmidt.lp_norm_sq
          (thermofieldDiagonalKernel_isHS (primeCriticalLocalHalfDensity p))
      _ = ‖primeCriticalLocalHalfDensity p‖ ^ 2 :=
        hsNormSq_thermofieldDiagonalKernel (primeCriticalLocalHalfDensity p)
      _ = 1 := norm_sq_geometricOccupationHalfDensity
        (primeRadialCriticalMass_nonneg p) (primeRadialCriticalMass_lt_one p)
  nlinarith [norm_nonneg (primeCriticalLocalThermofieldVector p)]

/-- Diagonal standard-form lift preserves Hilbert inner products. -/
theorem inner_thermofieldDiagonalLp
    (v w : lp (fun _ : ℕ => ℂ) 2) :
    inner ℂ
        (⟨thermofieldDiagonalKernel v,
          (thermofieldDiagonalKernel_isHS v).memℓp⟩ :
            lp (fun _ : ℕ × ℕ => ℂ) 2)
        (⟨thermofieldDiagonalKernel w,
          (thermofieldDiagonalKernel_isHS w).memℓp⟩ :
            lp (fun _ : ℕ × ℕ => ℂ) 2) =
      inner ℂ v w := by
  rw [← HilbertSchmidt.hsInner_eq_lp_inner
    (thermofieldDiagonalKernel_isHS v)
    (thermofieldDiagonalKernel_isHS w),
    HilbertSchmidt.hsInner, lp.inner_eq_tsum,
    (HilbertSchmidt.hsInner_summable
      (thermofieldDiagonalKernel_isHS v)
      (thermofieldDiagonalKernel_isHS w)).tsum_prod]
  apply tsum_congr
  intro i
  rw [tsum_eq_single i]
  · simp [thermofieldDiagonalKernel, RCLike.inner_apply, mul_comm]
  · intro j hji
    simp [thermofieldDiagonalKernel, Ne.symm hji]

/-- Unit reference family for the ordinary-prime incomplete tensor product. -/
def primeCriticalThermofieldReference (p : Nat.Primes) :
    HilbertUnitVector (PrimeThermofieldLocalHilbert p) :=
  ⟨primeCriticalLocalThermofieldVector p,
    norm_primeCriticalLocalThermofieldVector p⟩

/-- Canonical all-prime Wold standard-form incomplete tensor product from `(22)`. -/
abbrev PrimeWoldIncompleteTensorProduct : Type :=
  IncompleteTensorProduct PrimeThermofieldLocalHilbert
    primeCriticalThermofieldReference

/-- Distinguished all-prime critical Wold vector `Ω∞ᵂ`. -/
def primeWoldInfiniteReference : PrimeWoldIncompleteTensorProduct :=
  incompleteTensorReference PrimeThermofieldLocalHilbert
    primeCriticalThermofieldReference

theorem norm_primeWoldInfiniteReference :
    ‖primeWoldInfiniteReference‖ = 1 :=
  norm_incompleteTensorReference PrimeThermofieldLocalHilbert
    primeCriticalThermofieldReference

/-- Canonical image of a finite packet of local pure tensors. -/
def primeWoldFiniteTensorVector (S : Finset Nat.Primes)
    (v : ∀ p : Nat.Primes, PrimeThermofieldLocalHilbert p) :
    PrimeWoldIncompleteTensorProduct :=
  incompleteTensorVector PrimeThermofieldLocalHilbert
    primeCriticalThermofieldReference
    (IncompleteTensorElementary.ofFinset PrimeThermofieldLocalHilbert
      primeCriticalThermofieldReference S (fun p => v p.1))

/-- Exact pure-tensor inner law inside the completed all-prime carrier. -/
theorem inner_primeWoldFiniteTensorVector (S : Finset Nat.Primes)
    (v w : ∀ p : Nat.Primes, PrimeThermofieldLocalHilbert p) :
    inner ℂ (primeWoldFiniteTensorVector S w)
        (primeWoldFiniteTensorVector S v) =
      ∏ p ∈ S, inner ℂ (w p) (v p) := by
  rw [primeWoldFiniteTensorVector, primeWoldFiniteTensorVector,
    inner_incompleteTensorVector, incompleteTensorKernel]
  simp only [IncompleteTensorElementary.ofFinset, Finset.union_self]
  apply Finset.prod_congr rfl
  intro p hp
  simp [hp]

theorem primeRadialTwistedMass_nonneg (c : ℝ) (p : Nat.Primes) :
    0 ≤ primeRadialTwistedMass c p :=
  Real.rpow_nonneg (by exact_mod_cast p.2.pos.le) _

theorem primeRadialTwistedMass_lt_one
    {c : ℝ} (hcHalf : c < 1 / 2) (p : Nat.Primes) :
    primeRadialTwistedMass c p < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast p.2.one_lt) (by linarith)

/-- One-prime coherently twisted occupation half-density. -/
def primeTwistedLocalHalfDensity
    {c : ℝ} (hcHalf : c < 1 / 2) (p : Nat.Primes) :
    lp (fun _ : ℕ => ℂ) 2 :=
  geometricOccupationHalfDensity (primeRadialTwistedMass c p)
    (primeRadialTwistedMass_nonneg c p)
    (primeRadialTwistedMass_lt_one hcHalf p)

/-- Diagonal standard-form lift of the one-prime twisted Wold state. -/
def primeTwistedLocalThermofieldVector
    {c : ℝ} (hcHalf : c < 1 / 2) (p : Nat.Primes) :
    PrimeThermofieldLocalHilbert p :=
  ⟨thermofieldDiagonalKernel (primeTwistedLocalHalfDensity hcHalf p),
    (thermofieldDiagonalKernel_isHS
      (primeTwistedLocalHalfDensity hcHalf p)).memℓp⟩

theorem norm_primeTwistedLocalThermofieldVector
    {c : ℝ} (hcHalf : c < 1 / 2) (p : Nat.Primes) :
    ‖primeTwistedLocalThermofieldVector hcHalf p‖ = 1 := by
  have hsq : ‖primeTwistedLocalThermofieldVector hcHalf p‖ ^ 2 = 1 := by
    calc
      ‖primeTwistedLocalThermofieldVector hcHalf p‖ ^ 2 =
          HilbertSchmidt.hsNormSq
            (thermofieldDiagonalKernel
              (primeTwistedLocalHalfDensity hcHalf p)) :=
        HilbertSchmidt.lp_norm_sq
          (thermofieldDiagonalKernel_isHS
            (primeTwistedLocalHalfDensity hcHalf p))
      _ = ‖primeTwistedLocalHalfDensity hcHalf p‖ ^ 2 :=
        hsNormSq_thermofieldDiagonalKernel
          (primeTwistedLocalHalfDensity hcHalf p)
      _ = 1 := norm_sq_geometricOccupationHalfDensity
        (primeRadialTwistedMass_nonneg c p)
        (primeRadialTwistedMass_lt_one hcHalf p)
  nlinarith [norm_nonneg (primeTwistedLocalThermofieldVector hcHalf p)]

theorem inner_primeCriticalLocal_primeTwistedLocal
    {c : ℝ} (hcHalf : c < 1 / 2) (p : Nat.Primes) :
    inner ℂ (primeCriticalLocalThermofieldVector p)
        (primeTwistedLocalThermofieldVector hcHalf p) =
      (geometricHellingerAffinity (primeRadialCriticalMass p)
        (primeRadialTwistedMass c p) : ℂ) := by
  rw [primeCriticalLocalThermofieldVector,
    primeTwistedLocalThermofieldVector,
    inner_thermofieldDiagonalLp,
    primeCriticalLocalHalfDensity, primeTwistedLocalHalfDensity,
    inner_geometricOccupationHalfDensity]

/-- Cofinal twisted finite packet, embedded as an actual vector of the critical incomplete
tensor-product carrier. -/
def primeWoldTwistedFinitePacket
    {c : ℝ} (hcHalf : c < 1 / 2) (N : ℕ) :
    PrimeWoldIncompleteTensorProduct :=
  primeWoldFiniteTensorVector (GaloisForLFunctions.primesBelowSubtype N)
    (primeTwistedLocalThermofieldVector hcHalf)

theorem inner_primeWoldInfiniteReference_twistedFinitePacket
    {c : ℝ} (hcHalf : c < 1 / 2) (N : ℕ) :
    inner ℂ primeWoldInfiniteReference
        (primeWoldTwistedFinitePacket hcHalf N) =
      ∏ p ∈ GaloisForLFunctions.primesBelowSubtype N,
        (geometricHellingerAffinity (primeRadialCriticalMass p)
          (primeRadialTwistedMass c p) : ℂ) := by
  rw [primeWoldInfiniteReference, primeWoldTwistedFinitePacket,
    primeWoldFiniteTensorVector, incompleteTensorReference,
    inner_incompleteTensorVector, incompleteTensorKernel]
  simp only [IncompleteTensorElementary.ofFinset,
    IncompleteTensorElementary.reference, Finset.union_empty]
  apply Finset.prod_congr rfl
  intro p hp
  simpa [hp, primeCriticalThermofieldReference] using
    inner_primeCriticalLocal_primeTwistedLocal hcHalf p

theorem prod_primesBelowSubtype_geometricHellingerAffinity
    {c : ℝ} (hcHalf : c < 1 / 2) (N : ℕ) :
    (∏ p ∈ GaloisForLFunctions.primesBelowSubtype N,
        geometricHellingerAffinity (primeRadialCriticalMass p)
          (primeRadialTwistedMass c p)) =
      primeValuationHellingerBelow c N := by
  rw [GaloisForLFunctions.primesBelowSubtype, Finset.prod_map]
  rw [show (Nat.primesBelow N).attach = Finset.univ by ext p; simp]
  convert prod_geometricHellingerAffinity_primeRadial hcHalf N using 1
  apply Finset.prod_congr rfl
  intro p hp
  congr 3

/-- Exact finite overlap `(24)` realized inside the completed critical carrier. -/
theorem inner_primeWoldInfiniteReference_twistedFinitePacket_eq
    {c : ℝ} (hcHalf : c < 1 / 2) (N : ℕ) :
    inner ℂ primeWoldInfiniteReference
        (primeWoldTwistedFinitePacket hcHalf N) =
      (primeValuationHellingerBelow c N : ℂ) := by
  rw [inner_primeWoldInfiniteReference_twistedFinitePacket]
  exact_mod_cast
    prod_primesBelowSubtype_geometricHellingerAffinity hcHalf N

/-- Literal incomplete-product sector fracture: critical-reference overlaps with cofinal twisted
packets tend to one exactly in the critical sector and zero in every other radial sector. -/
theorem tendsto_inner_primeWoldInfiniteReference_twistedFinitePacket
    {c : ℝ} (hcHalf : c < 1 / 2) :
    Tendsto (fun N => inner ℂ primeWoldInfiniteReference
        (primeWoldTwistedFinitePacket hcHalf N)) atTop
      (𝓝 ((if c = 0 then (1 : ℝ) else 0 : ℝ) : ℂ)) := by
  have h := (Complex.continuous_ofReal.tendsto
    (if c = 0 then (1 : ℝ) else 0)).comp
      (tendsto_primeValuationHellingerBelow_ite hcHalf)
  refine h.congr' (Filter.Eventually.of_forall fun N => ?_)
  exact (inner_primeWoldInfiniteReference_twistedFinitePacket_eq hcHalf N).symm

theorem inner_primeWoldTwistedFinitePacket_of_le
    {c : ℝ} (hcHalf : c < 1 / 2) {N M : ℕ} (hNM : N ≤ M) :
    inner ℂ (primeWoldTwistedFinitePacket hcHalf N)
        (primeWoldTwistedFinitePacket hcHalf M) =
      (∏ p ∈ GaloisForLFunctions.primesBelowSubtype M \
          GaloisForLFunctions.primesBelowSubtype N,
        (geometricHellingerAffinity (primeRadialCriticalMass p)
          (primeRadialTwistedMass c p) : ℂ)) := by
  classical
  have hsub : GaloisForLFunctions.primesBelowSubtype N ⊆
      GaloisForLFunctions.primesBelowSubtype M :=
    monotone_primesBelowSubtype hNM
  rw [primeWoldTwistedFinitePacket, primeWoldTwistedFinitePacket,
    primeWoldFiniteTensorVector, primeWoldFiniteTensorVector,
    inner_incompleteTensorVector, incompleteTensorKernel]
  simp only [IncompleteTensorElementary.ofFinset]
  rw [Finset.union_eq_left.mpr hsub]
  calc
    (∏ p ∈ GaloisForLFunctions.primesBelowSubtype M,
        inner ℂ
          (if hp : p ∈ GaloisForLFunctions.primesBelowSubtype N then
            primeTwistedLocalThermofieldVector hcHalf p
          else (primeCriticalThermofieldReference p).val)
          (if hp : p ∈ GaloisForLFunctions.primesBelowSubtype M then
            primeTwistedLocalThermofieldVector hcHalf p
          else (primeCriticalThermofieldReference p).val)) =
        ∏ p ∈ GaloisForLFunctions.primesBelowSubtype M \
            GaloisForLFunctions.primesBelowSubtype N,
          inner ℂ
            (if hp : p ∈ GaloisForLFunctions.primesBelowSubtype N then
              primeTwistedLocalThermofieldVector hcHalf p
            else (primeCriticalThermofieldReference p).val)
            (if hp : p ∈ GaloisForLFunctions.primesBelowSubtype M then
              primeTwistedLocalThermofieldVector hcHalf p
            else (primeCriticalThermofieldReference p).val) := by
      symm
      apply Finset.prod_subset Finset.sdiff_subset
      intro p hpM hpNot
      have hpN : p ∈ GaloisForLFunctions.primesBelowSubtype N := by
        simp only [Finset.mem_sdiff, hpM, true_and, not_not] at hpNot
        exact hpNot
      simp [hpN, hpM, inner_self_eq_norm_sq_to_K,
        norm_primeTwistedLocalThermofieldVector hcHalf p]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p hp
      have hpM := (Finset.mem_sdiff.mp hp).1
      have hpN := (Finset.mem_sdiff.mp hp).2
      simp [hpN, hpM, primeCriticalThermofieldReference]
      exact inner_primeCriticalLocal_primeTwistedLocal hcHalf p

theorem primeValuationHellingerBelow_pos
    {c : ℝ} (hcHalf : c < 1 / 2) (N : ℕ) :
    0 < primeValuationHellingerBelow c N := by
  rw [← prod_primesBelowSubtype_geometricHellingerAffinity hcHalf N]
  apply Finset.prod_pos
  intro p hp
  rw [geometricHellingerAffinity]
  apply div_pos
  · apply Real.sqrt_pos.2
    exact mul_pos
      (sub_pos.mpr (primeRadialCriticalMass_lt_one p))
      (sub_pos.mpr (primeRadialTwistedMass_lt_one hcHalf p))
  · have hmul : primeRadialCriticalMass p * primeRadialTwistedMass c p < 1 := by
      nlinarith [primeRadialCriticalMass_nonneg p,
        primeRadialCriticalMass_lt_one p,
        primeRadialTwistedMass_nonneg c p,
        primeRadialTwistedMass_lt_one hcHalf p]
    have hsqrt : Real.sqrt
        (primeRadialCriticalMass p * primeRadialTwistedMass c p) < 1 := by
      rw [Real.sqrt_lt' zero_lt_one]
      simpa using hmul
    linarith

theorem inner_primeWoldTwistedFinitePacket_eq_div_of_le
    {c : ℝ} (hcHalf : c < 1 / 2) {N M : ℕ} (hNM : N ≤ M) :
    inner ℂ (primeWoldTwistedFinitePacket hcHalf N)
        (primeWoldTwistedFinitePacket hcHalf M) =
      ((primeValuationHellingerBelow c M /
        primeValuationHellingerBelow c N : ℝ) : ℂ) := by
  rw [inner_primeWoldTwistedFinitePacket_of_le hcHalf hNM]
  have hsub : GaloisForLFunctions.primesBelowSubtype N ⊆
      GaloisForLFunctions.primesBelowSubtype M :=
    monotone_primesBelowSubtype hNM
  have hprod := Finset.prod_sdiff hsub
    (f := fun p => geometricHellingerAffinity (primeRadialCriticalMass p)
      (primeRadialTwistedMass c p))
  rw [prod_primesBelowSubtype_geometricHellingerAffinity hcHalf N,
    prod_primesBelowSubtype_geometricHellingerAffinity hcHalf M] at hprod
  push_cast
  rw [eq_div_iff]
  · simpa [mul_comm] using congrArg Complex.ofReal hprod
  · exact_mod_cast (ne_of_gt (primeValuationHellingerBelow_pos hcHalf N))

theorem norm_primeWoldTwistedFinitePacket
    {c : ℝ} (hcHalf : c < 1 / 2) (N : ℕ) :
    ‖primeWoldTwistedFinitePacket hcHalf N‖ = 1 := by
  have hinner : inner ℂ (primeWoldTwistedFinitePacket hcHalf N)
      (primeWoldTwistedFinitePacket hcHalf N) = 1 := by
    rw [primeWoldTwistedFinitePacket,
      inner_primeWoldFiniteTensorVector]
    simp [inner_self_eq_norm_sq_to_K,
      norm_primeTwistedLocalThermofieldVector hcHalf]
  have hsq : ‖primeWoldTwistedFinitePacket hcHalf N‖ ^ 2 =
      RCLike.re (inner ℂ (primeWoldTwistedFinitePacket hcHalf N)
        (primeWoldTwistedFinitePacket hcHalf N)) :=
    norm_sq_eq_re_inner _
  rw [hinner] at hsq
  norm_num at hsq
  rcases hsq with hsq | hsq
  · exact hsq
  · linarith [norm_nonneg (primeWoldTwistedFinitePacket hcHalf N)]

theorem primeWoldTwistedFinitePacket_zero
    (hcHalf : (0 : ℝ) < 1 / 2) (N : ℕ) :
    primeWoldTwistedFinitePacket hcHalf N = primeWoldInfiniteReference := by
  let v := primeWoldTwistedFinitePacket hcHalf N
  let Ω := primeWoldInfiniteReference
  have hv : ‖v‖ = 1 := norm_primeWoldTwistedFinitePacket hcHalf N
  have hΩ : ‖Ω‖ = 1 := norm_primeWoldInfiniteReference
  have hΩv : inner ℂ Ω v = 1 := by
    change inner ℂ primeWoldInfiniteReference
      (primeWoldTwistedFinitePacket hcHalf N) = 1
    rw [inner_primeWoldInfiniteReference_twistedFinitePacket_eq,
      primeValuationHellingerBelow_zero]
    norm_num
  have hvΩ : inner ℂ v Ω = 1 := by
    rw [← inner_conj_symm]
    simp [hΩv]
  have hdiff : inner ℂ (v - Ω) (v - Ω) = 0 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right]
    rw [hΩv, hvΩ, inner_self_eq_norm_sq_to_K,
      inner_self_eq_norm_sq_to_K, hv, hΩ]
    norm_num
  have hnormsq : ‖v - Ω‖ ^ 2 = 0 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), hdiff]
    norm_num
  have hnorm : ‖v - Ω‖ = 0 := by nlinarith [norm_nonneg (v - Ω)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

theorem tendsto_primeWoldTwistedFinitePacket_zero
    (hcHalf : (0 : ℝ) < 1 / 2) :
    Tendsto (primeWoldTwistedFinitePacket hcHalf) atTop
      (𝓝 primeWoldInfiniteReference) := by
  refine tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun N => ?_)
  exact (primeWoldTwistedFinitePacket_zero hcHalf N).symm

theorem tendsto_inner_primeWoldTwistedFinitePacket_fixed_zero_of_ne
    {c : ℝ} (hcHalf : c < 1 / 2) (hc0 : c ≠ 0) (N : ℕ) :
    Tendsto (fun M => inner ℂ (primeWoldTwistedFinitePacket hcHalf N)
        (primeWoldTwistedFinitePacket hcHalf M)) atTop (𝓝 0) := by
  have hreal : Tendsto (fun M =>
      primeValuationHellingerBelow c M /
        primeValuationHellingerBelow c N) atTop (𝓝 0) := by
    simpa using (tendsto_primeValuationHellingerBelow_zero_of_ne hcHalf hc0).div_const
      (primeValuationHellingerBelow c N)
  have hcomplex := (Complex.continuous_ofReal.tendsto 0).comp hreal
  refine hcomplex.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop N] with M hNM
  exact (inner_primeWoldTwistedFinitePacket_eq_div_of_le hcHalf hNM).symm

/-- Noncritical radial packets do not converge in the critical incomplete tensor-product sector. -/
theorem not_exists_tendsto_primeWoldTwistedFinitePacket_of_ne
    {c : ℝ} (hcHalf : c < 1 / 2) (hc0 : c ≠ 0) :
    ¬ ∃ v : PrimeWoldIncompleteTensorProduct,
      Tendsto (primeWoldTwistedFinitePacket hcHalf) atTop (𝓝 v) := by
  rintro ⟨v, hv⟩
  have hnorm_one : Tendsto
      (fun N => ‖primeWoldTwistedFinitePacket hcHalf N‖) atTop (𝓝 1) := by
    refine tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun N => ?_)
    exact (norm_primeWoldTwistedFinitePacket hcHalf N).symm
  have hvnorm : ‖v‖ = 1 :=
    tendsto_nhds_unique hv.norm hnorm_one
  have horth : ∀ N, inner ℂ (primeWoldTwistedFinitePacket hcHalf N) v = 0 := by
    intro N
    have hconst : Tendsto
        (fun _ : ℕ => primeWoldTwistedFinitePacket hcHalf N) atTop
        (𝓝 (primeWoldTwistedFinitePacket hcHalf N)) := tendsto_const_nhds
    have htoV : Tendsto
        (fun M => inner ℂ (primeWoldTwistedFinitePacket hcHalf N)
          (primeWoldTwistedFinitePacket hcHalf M)) atTop
        (𝓝 (inner ℂ (primeWoldTwistedFinitePacket hcHalf N) v)) :=
      hconst.inner hv
    exact tendsto_nhds_unique htoV
      (tendsto_inner_primeWoldTwistedFinitePacket_fixed_zero_of_ne hcHalf hc0 N)
  have hzero : Tendsto
      (fun N => inner ℂ (primeWoldTwistedFinitePacket hcHalf N) v)
      atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun N => ?_)
    exact (horth N).symm
  have hself : Tendsto
      (fun N => inner ℂ (primeWoldTwistedFinitePacket hcHalf N) v)
      atTop (𝓝 (inner ℂ v v)) := hv.inner tendsto_const_nhds
  have hinnerzero : inner ℂ v v = 0 := tendsto_nhds_unique hself hzero
  rw [inner_self_eq_norm_sq_to_K, hvnorm] at hinnerzero
  norm_num at hinnerzero

/-- Exact vector-sector/Kakutani criterion: cofinal twisted packets converge in the critical
incomplete tensor-product carrier exactly on the critical ray. -/
theorem exists_tendsto_primeWoldTwistedFinitePacket_iff
    {c : ℝ} (hcHalf : c < 1 / 2) :
    (∃ v : PrimeWoldIncompleteTensorProduct,
      Tendsto (primeWoldTwistedFinitePacket hcHalf) atTop (𝓝 v)) ↔ c = 0 := by
  constructor
  · intro h
    by_contra hc0
    exact not_exists_tendsto_primeWoldTwistedFinitePacket_of_ne hcHalf hc0 h
  · rintro rfl
    exact ⟨primeWoldInfiniteReference,
      tendsto_primeWoldTwistedFinitePacket_zero hcHalf⟩

end

end RHTower
