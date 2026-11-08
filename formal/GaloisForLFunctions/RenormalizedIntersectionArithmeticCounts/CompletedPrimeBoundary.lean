import GaloisForLFunctions.EffectiveScalingGeometry.DirichletChainGauge
import GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix
import GaloisForLFunctions.HTGeometry.RankOneHilbertSchmidt
import GaloisForLFunctions.RHTower.Sieve.EulerLogCompare
import GaloisForLFunctions.HTGeometry.DiagonalCompactOperator
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# The exact Hilbert domain of the prime Dirichlet boundary

Finite prime chains carry squared norm `Σ p^δ |a_p|²` and the original
augmentation `Σ p^(-s) a_p`. Their normalized embedding is injective and dense.
A bounded extension exists exactly when `2 Re(s)+δ>1`; it is unique and its
squared norm is the prime Dirichlet sum at that exponent. Below this open
half-plane, explicit finite Riesz packets have boundary one and norm tending
to zero. No closed partial linear extension can then preserve the boundary.

The arithmetic gauge identifies weighted finite graphs with the unweighted
graph at `s+δ/2`. These are degree-one domain statements; no higher homology
or zero-detection comparison is assumed.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open RHTower EffectiveScalingGeometry

/-- The Hilbert completion of normalized prime coefficients. -/
abbrev PrimeChainHilbert := lp (fun _ : Nat.Primes=>ℂ) 2

/-- Finite prime chains embedded in their normalized Hilbert completion. -/
def primeChainHilbertEmbedding : (Nat.Primes →₀ ℂ) →ₗ[ℂ] PrimeChainHilbert :=
  Finsupp.linearCombination ℂ (HilbertSchmidt.lpBasis Nat.Primes)

theorem primeChainHilbertEmbedding_single (p : Nat.Primes) (c : ℂ) :
    primeChainHilbertEmbedding (Finsupp.single p c)=c • HilbertSchmidt.lpBasis Nat.Primes p := by
  simp only [primeChainHilbertEmbedding,Finsupp.linearCombination_single]

/-- The actual Dirichlet boundary coefficients are square summable exactly beyond one half. -/
theorem primeBoundary_square_summable_iff (s : ℂ) :
    Summable (fun p : Nat.Primes=>‖(p:ℂ)^(-s)‖^2) ↔ 1/2<s.re := by
  have he (p : Nat.Primes) : ‖(p:ℂ)^(-s)‖^2=(p:ℝ)^(-(2*s.re)) :=
    RHTower.Sieve.norm_prime_cpow_sq_eq p.property.pos s
  simp_rw [he]
  rw [Nat.Primes.summable_rpow]
  constructor <;> intro h <;> linarith only [h]

/-- The Riesz vector for the prime augmentation in its exact bounded range. -/
def primeBoundaryRieszVector (s : ℂ) (hs : 1/2<s.re) : PrimeChainHilbert :=
  ⟨fun p=>star ((p:ℂ)^(-s)),HilbertSchmidt.memℓp_of_sq (by
    simpa only [norm_star] using (primeBoundary_square_summable_iff s).mpr hs)⟩

/-- The bounded extension of the original prime Dirichlet augmentation. -/
def primeBoundaryExtension (s : ℂ) (hs : 1/2<s.re) : PrimeChainHilbert →L[ℂ] ℂ :=
  InnerProductSpace.toDual ℂ PrimeChainHilbert (primeBoundaryRieszVector s hs)

/-- The extension retains every original prime coefficient. -/
theorem primeBoundaryExtension_basis (s : ℂ) (hs : 1/2<s.re) (p : Nat.Primes) :
    primeBoundaryExtension s hs (HilbertSchmidt.lpBasis Nat.Primes p)=(p:ℂ)^(-s) := by
  change inner ℂ (primeBoundaryRieszVector s hs) (HilbertSchmidt.lpBasis Nat.Primes p)=_
  rw [←inner_conj_symm,HilbertSchmidt.lpBasis_apply,lp.inner_single_left]
  simp [primeBoundaryRieszVector]

/-- The original finite-chain boundary is the restriction of the constructed operator. -/
theorem primeBoundaryExtension_finite (s : ℂ) (hs : 1/2<s.re) :
    (primeBoundaryExtension s hs).toLinearMap.comp primeChainHilbertEmbedding=
      dirichletPrimeChainFunctional s := by
  apply Finsupp.lhom_ext
  intro p c
  simp only [LinearMap.comp_apply,ContinuousLinearMap.coe_coe,primeChainHilbertEmbedding_single,
    map_smul,primeBoundaryExtension_basis,dirichletPrimeChainFunctional,
    Finsupp.linearCombination_single,smul_eq_mul]

/-- The exact norm is the square root of the prime Dirichlet series at twice the real part. -/
theorem primeBoundaryExtension_norm_sq (s : ℂ) (hs : 1/2<s.re) :
    ‖primeBoundaryExtension s hs‖^2=∑'p : Nat.Primes,(p:ℝ)^(-(2*s.re)) := by
  rw [primeBoundaryExtension,LinearIsometryEquiv.norm_map,HilbertSchmidt.lp_norm_sq_eq]
  apply tsum_congr
  intro p
  change ‖star ((p:ℂ)^(-s))‖^2=_
  rw [norm_star]
  exact RHTower.Sieve.norm_prime_cpow_sq_eq p.property.pos s

/-- Bounded extension of the actual finite-chain augmentation has a sharp half-plane. -/
theorem primeBoundary_bounded_extension_iff (s : ℂ) :
    (∃φ : PrimeChainHilbert →L[ℂ] ℂ,
      φ.toLinearMap.comp primeChainHilbertEmbedding=dirichletPrimeChainFunctional s) ↔
        1/2<s.re := by
  constructor
  · rintro ⟨φ,hφ⟩
    have hb (p : Nat.Primes) : φ (HilbertSchmidt.lpBasis Nat.Primes p)=(p:ℂ)^(-s) := by
      have h:=LinearMap.congr_fun hφ (Finsupp.single p 1)
      simpa only [LinearMap.comp_apply,ContinuousLinearMap.coe_coe,primeChainHilbertEmbedding_single,
        one_smul,dirichletPrimeChainFunctional,Finsupp.linearCombination_single] using h
    apply (primeBoundary_square_summable_iff s).mp
    simpa only [hb] using HTGeometry.summable_norm_apply_sq (HilbertSchmidt.lpBasis Nat.Primes) φ
  · intro hs
    exact ⟨primeBoundaryExtension s hs,primeBoundaryExtension_finite s hs⟩

#print axioms primeBoundary_square_summable_iff
#print axioms primeBoundaryExtension_finite
#print axioms primeBoundaryExtension_norm_sq
#print axioms primeBoundary_bounded_extension_iff
/-- The finite Riesz packet of the actual Dirichlet augmentation. -/
def primeBoundaryPacket (s : ℂ) (S : Finset Nat.Primes) : Nat.Primes →₀ ℂ :=
  ∑p∈S,Finsupp.single p (star ((p:ℂ)^(-s)))

/-- The packet's boundary equals the exact finite coefficient square mass. -/
theorem primeBoundaryPacket_boundary (s : ℂ) (S : Finset Nat.Primes) :
    dirichletPrimeChainFunctional s (primeBoundaryPacket s S)=
      ((∑p∈S,‖(p:ℂ)^(-s)‖^2 : ℝ):ℂ) := by
  simp only [primeBoundaryPacket,map_sum,dirichletPrimeChainFunctional,
    Finsupp.linearCombination_single,smul_eq_mul]
  push_cast
  apply sum_congr rfl
  intro p hp
  have hz (z : ℂ) : star z*z=(‖z‖:ℂ)^2 := by
    rw [mul_comm]
    change z * (starRingEnd ℂ) z = _
    rw [Complex.mul_conj,←Complex.sq_norm]
    push_cast
    rfl
  exact hz _

/-- The same coefficient square mass is the squared Hilbert norm of the packet. -/
theorem primeBoundaryPacket_norm_sq (s : ℂ) (S : Finset Nat.Primes) :
    ‖primeChainHilbertEmbedding (primeBoundaryPacket s S)‖^2=
      ∑p∈S,‖(p:ℂ)^(-s)‖^2 := by
  have he : primeChainHilbertEmbedding (primeBoundaryPacket s S)=
      ∑p∈S,star ((p:ℂ)^(-s)) • HilbertSchmidt.lpBasis Nat.Primes p := by
    simp only [primeBoundaryPacket,map_sum,primeChainHilbertEmbedding_single]
  rw [he]
  rw [HTGeometry.norm_sq_sum_smul_orthonormal
    (HilbertSchmidt.lpBasis Nat.Primes).orthonormal]
  simp only [norm_star]

/-- At or below one half, finite coefficient square masses have no upper bound. -/
theorem primeBoundary_unbounded_mass (s : ℂ) (hs : s.re≤1/2) (M : ℝ) :
    ∃S : Finset Nat.Primes,M<∑p∈S,‖(p:ℂ)^(-s)‖^2 := by
  by_contra h
  push Not at h
  have hsum:=summable_of_sum_le (fun p : Nat.Primes=>sq_nonneg ‖(p:ℂ)^(-s)‖) h
  exact (not_lt_of_ge hs) ((primeBoundary_square_summable_iff s).mp hsum)

/-- Unit boundary can be carried by finite chains of arbitrarily small squared Hilbert norm. -/
theorem primeBoundary_unit_response_small_norm (s : ℂ) (hs : s.re≤1/2)
    (ε : ℝ) (hε : 0<ε) :
    ∃a : Nat.Primes →₀ ℂ,dirichletPrimeChainFunctional s a=1 ∧
      ‖primeChainHilbertEmbedding a‖^2<ε := by
  obtain ⟨S,hS⟩:=primeBoundary_unbounded_mass s hs (1/ε)
  let A : ℝ := ∑p∈S,‖(p:ℂ)^(-s)‖^2
  have hA : 0<A := lt_trans (one_div_pos.mpr hε) hS
  refine ⟨(A:ℂ)⁻¹ • primeBoundaryPacket s S,?_,?_⟩
  · rw [map_smul,primeBoundaryPacket_boundary]
    change (A:ℂ)⁻¹*(A:ℂ)=1
    exact inv_mul_cancel₀ (by exact_mod_cast hA.ne')
  · rw [map_smul,norm_smul,mul_pow,primeBoundaryPacket_norm_sq,norm_inv,
      Complex.norm_real,Real.norm_of_nonneg hA.le]
    change (A⁻¹)^2*A<ε
    have he : (A⁻¹)^2*A=1/A := by field_simp [hA.ne']
    rw [he]
    apply (div_lt_iff₀ hA).mpr
    have hh : 1<A*ε := (div_lt_iff₀ hε).mp hS
    nlinarith only [hh]

#print axioms primeBoundaryPacket_boundary
#print axioms primeBoundaryPacket_norm_sq
#print axioms primeBoundary_unit_response_small_norm

/-- The graph of the actual augmentation on finite prime chains. -/
def primeBoundaryGraph (s : ℂ) : Set (PrimeChainHilbert × ℂ) :=
  Set.range (fun a : Nat.Primes →₀ ℂ =>
    (primeChainHilbertEmbedding a,dirichletPrimeChainFunctional s a))

/-- At the critical half-plane, graph closure acquires a nonzero vertical vector. -/
theorem primeBoundary_graph_closure_unit (s : ℂ) (hs : s.re≤1/2) :
    (0,1)∈closure (primeBoundaryGraph s) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨a,ha,hna⟩:=primeBoundary_unit_response_small_norm s hs (ε^2) (sq_pos_of_pos hε)
  refine ⟨(primeChainHilbertEmbedding a,dirichletPrimeChainFunctional s a),⟨a,rfl⟩,?_⟩
  have hn : ‖primeChainHilbertEmbedding a‖<ε := by
    nlinarith only [hna,norm_nonneg (primeChainHilbertEmbedding a),hε]
  simpa only [ha,Prod.dist_eq,dist_zero_left,dist_zero_right,dist_self,
    max_eq_left (norm_nonneg _)] using hn

/-- No closed linear graph can extend the finite arithmetic boundary at or below one half. -/
theorem primeBoundary_no_closed_extension (s : ℂ) (hs : s.re≤1/2)
    (D : Submodule ℂ PrimeChainHilbert) (f : D →ₗ[ℂ] ℂ)
    (hfinite : ∀a,primeChainHilbertEmbedding a∈D)
    (hagree : ∀a,f ⟨primeChainHilbertEmbedding a,hfinite a⟩=dirichletPrimeChainFunctional s a) :
    ¬IsClosed (Set.range (fun u : D => (u.val,f u))) := by
  intro hc
  have hsub : primeBoundaryGraph s⊆Set.range (fun u : D => (u.val,f u)) := by
    rintro z ⟨a,rfl⟩
    refine ⟨⟨primeChainHilbertEmbedding a,hfinite a⟩,?_⟩
    exact Prod.ext rfl (hagree a)
  have hcl:=closure_minimal hsub hc
  obtain ⟨u,hu⟩:=hcl (primeBoundary_graph_closure_unit s hs)
  have hu0 : u=0 := Subtype.ext (congrArg Prod.fst hu)
  have hh:=congrArg Prod.snd hu
  change f u=1 at hh
  rw [hu0,map_zero] at hh
  exact zero_ne_one hh

#print axioms primeBoundary_graph_closure_unit
#print axioms primeBoundary_no_closed_extension

/-- A prime gauge shifts the parameter of the original augmentation by the opposite amount. -/
theorem primeBoundary_gauge_shift (s t : ℂ) :
    (dirichletPrimeChainFunctional s).comp (dirichletVertexGauge t)=
      dirichletPrimeChainFunctional (s-t) := by
  apply Finsupp.lhom_ext
  intro p c
  simp only [LinearMap.comp_apply,dirichletVertexGauge_single,dirichletPrimeChainFunctional,
    Finsupp.linearCombination_single,smul_eq_mul]
  have hp : (p:ℂ)≠0 := by exact_mod_cast p.property.ne_zero
  calc ((p:ℂ)^t*c)*(p:ℂ)^(-s)=c*((p:ℂ)^t*(p:ℂ)^(-s)) := by ring
       _ = c*(p:ℂ)^(t+-s) := by rw [←Complex.cpow_add _ _ hp]
       _ = _ := by congr 2; ring

/-- The normalized embedding of finite chains with conductor square weight `p^δ`. -/
def primeWeightedChainEmbedding (δ : ℝ) : (Nat.Primes →₀ ℂ) →ₗ[ℂ] PrimeChainHilbert :=
  primeChainHilbertEmbedding.comp (dirichletVertexGauge ((δ/2:ℝ):ℂ))

/-- A weighted prime atom is the canonical basis vector scaled by its square-root weight. -/
theorem primeWeightedChainEmbedding_single (δ : ℝ) (p : Nat.Primes) (c : ℂ) :
    primeWeightedChainEmbedding δ (Finsupp.single p c)=
      ((p:ℂ)^((δ/2:ℝ):ℂ)*c) • HilbertSchmidt.lpBasis Nat.Primes p := by
  rw [primeWeightedChainEmbedding,LinearMap.comp_apply,dirichletVertexGauge_single,
    primeChainHilbertEmbedding_single]

/-- Every weighted arithmetic atom has precisely its prescribed conductor norm. -/
theorem primeWeightedChainEmbedding_single_norm_sq (δ : ℝ) (p : Nat.Primes) (c : ℂ) :
    ‖primeWeightedChainEmbedding δ (Finsupp.single p c)‖^2=(p:ℝ)^δ*‖c‖^2 := by
  rw [primeWeightedChainEmbedding_single,norm_smul,
    (HilbertSchmidt.lpBasis Nat.Primes).orthonormal.norm_eq_one,mul_one,norm_mul,mul_pow,
    Complex.norm_natCast_cpow_of_pos p.property.pos,Complex.ofReal_re,pow_two]
  have hp : (0:ℝ)<p := by exact_mod_cast p.property.pos
  rw [←Real.rpow_add hp]
  congr 2
  ring

/-- Finite chains retain exactly the original conductor-weighted square mass. -/
theorem primeWeightedChainEmbedding_norm_sq (δ : ℝ) (a : Nat.Primes →₀ ℂ) :
    ‖primeWeightedChainEmbedding δ a‖^2=
      ∑p∈a.support,(p:ℝ)^δ*‖a p‖^2 := by
  have he : primeWeightedChainEmbedding δ=Finsupp.linearCombination ℂ
      (fun p : Nat.Primes=>(p:ℂ)^((δ/2:ℝ):ℂ) • HilbertSchmidt.lpBasis Nat.Primes p) := by
    apply Finsupp.lhom_ext
    intro p c
    rw [primeWeightedChainEmbedding_single,Finsupp.linearCombination_single,smul_smul]
    congr 1
    ring
  rw [he,Finsupp.linearCombination_apply]
  change ‖∑p∈a.support,a p • ((p:ℂ)^((δ/2:ℝ):ℂ) •
    HilbertSchmidt.lpBasis Nat.Primes p)‖^2=_
  simp only [smul_smul]
  rw [HTGeometry.norm_sq_sum_smul_orthonormal
    (HilbertSchmidt.lpBasis Nat.Primes).orthonormal]
  apply sum_congr rfl
  intro p hp
  have h:=primeWeightedChainEmbedding_single_norm_sq δ p (a p)
  rw [primeWeightedChainEmbedding_single,norm_smul,
    (HilbertSchmidt.lpBasis Nat.Primes).orthonormal.norm_eq_one,mul_one] at h
  simpa only [mul_comm (a p) ((p:ℂ)^((δ/2:ℝ):ℂ))] using h

/-- Bounded weighted extension is equivalent to ordinary extension at the shifted parameter. -/
theorem primeWeightedBoundary_extension_iff_shift (s : ℂ) (δ : ℝ)
    (φ : PrimeChainHilbert →L[ℂ] ℂ) :
    φ.toLinearMap.comp (primeWeightedChainEmbedding δ)=dirichletPrimeChainFunctional s ↔
      φ.toLinearMap.comp primeChainHilbertEmbedding=
        dirichletPrimeChainFunctional (s+((δ/2:ℝ):ℂ)) := by
  let t : ℂ := ((δ/2:ℝ):ℂ)
  constructor
  · intro h
    change (φ.toLinearMap.comp primeChainHilbertEmbedding).comp (dirichletVertexGauge t)=_ at h
    have he:=congrArg (fun L : (Nat.Primes →₀ ℂ) →ₗ[ℂ] ℂ=>
      L.comp (dirichletVertexGauge (-t))) h
    rw [LinearMap.comp_assoc,dirichletVertexGauge_add,add_neg_cancel,
      dirichletVertexGauge_zero,LinearMap.comp_id,primeBoundary_gauge_shift,sub_neg_eq_add] at he
    exact he
  · intro h
    change (φ.toLinearMap.comp primeChainHilbertEmbedding).comp (dirichletVertexGauge t)=_
    rw [h,primeBoundary_gauge_shift,add_sub_cancel_right]

/-- The actual conductor-weighted boundary extends exactly when `2 Re(s)+δ>1`. -/
theorem primeWeightedBoundary_bounded_extension_iff (s : ℂ) (δ : ℝ) :
    (∃φ : PrimeChainHilbert →L[ℂ] ℂ,
      φ.toLinearMap.comp (primeWeightedChainEmbedding δ)=dirichletPrimeChainFunctional s) ↔
        1<2*s.re+δ := by
  simp_rw [primeWeightedBoundary_extension_iff_shift]
  rw [primeBoundary_bounded_extension_iff]
  simp only [Complex.add_re,Complex.ofReal_re]
  constructor <;> intro h <;> linarith only [h]

/-- The original weighted finite graph, retaining the unshifted arithmetic boundary. -/
def primeWeightedBoundaryGraph (s : ℂ) (δ : ℝ) : Set (PrimeChainHilbert × ℂ) :=
  Set.range (fun a : Nat.Primes →₀ ℂ=>
    (primeWeightedChainEmbedding δ a,dirichletPrimeChainFunctional s a))

/-- The graph parameter shift is exact on all finite arithmetic chains. -/
theorem primeWeightedBoundaryGraph_eq_shift (s : ℂ) (δ : ℝ) :
    primeWeightedBoundaryGraph s δ=primeBoundaryGraph (s+((δ/2:ℝ):ℂ)) := by
  let t : ℂ := ((δ/2:ℝ):ℂ)
  ext z
  constructor
  · rintro ⟨a,rfl⟩
    refine ⟨dirichletVertexGauge t a,?_⟩
    apply Prod.ext
    · rfl
    · have h:=LinearMap.congr_fun (primeBoundary_gauge_shift (s+t) t) a
      simpa only [LinearMap.comp_apply,add_sub_cancel_right] using h
  · rintro ⟨a,rfl⟩
    refine ⟨dirichletVertexGauge (-t) a,?_⟩
    apply Prod.ext
    · change primeChainHilbertEmbedding
        ((dirichletVertexGauge t).comp (dirichletVertexGauge (-t)) a)=_
      rw [dirichletVertexGauge_add,add_neg_cancel,dirichletVertexGauge_zero,LinearMap.id_apply]
    · have h:=LinearMap.congr_fun (primeBoundary_gauge_shift s (-t)) a
      simpa only [LinearMap.comp_apply,sub_neg_eq_add] using h

/-- The entire closed critical region has a nonzero vertical graph fibre. -/
theorem primeWeightedBoundary_graph_closure_unit (s : ℂ) (δ : ℝ)
    (h : 2*s.re+δ≤1) : (0,1)∈closure (primeWeightedBoundaryGraph s δ) := by
  rw [primeWeightedBoundaryGraph_eq_shift]
  apply primeBoundary_graph_closure_unit
  simp only [Complex.add_re,Complex.ofReal_re]
  linarith only [h]

#print axioms primeWeightedChainEmbedding_norm_sq
#print axioms primeWeightedChainEmbedding_single_norm_sq
#print axioms primeWeightedBoundary_bounded_extension_iff
#print axioms primeWeightedBoundaryGraph_eq_shift
#print axioms primeWeightedBoundary_graph_closure_unit

/-- The bounded weighted extension is explicitly the shifted Riesz functional. -/
def primeWeightedBoundaryExtension (s : ℂ) (δ : ℝ) (h : 1<2*s.re+δ) :
    PrimeChainHilbert →L[ℂ] ℂ :=
  primeBoundaryExtension (s+((δ/2:ℝ):ℂ)) (by
    simp only [Complex.add_re,Complex.ofReal_re]
    linarith only [h])

theorem primeWeightedBoundaryExtension_finite (s : ℂ) (δ : ℝ) (h : 1<2*s.re+δ) :
    (primeWeightedBoundaryExtension s δ h).toLinearMap.comp (primeWeightedChainEmbedding δ)=
      dirichletPrimeChainFunctional s := by
  apply (primeWeightedBoundary_extension_iff_shift s δ _).mpr
  exact primeBoundaryExtension_finite _ _

/-- The exact weighted boundary norm is the prime Dirichlet series at `2 Re(s)+δ`. -/
theorem primeWeightedBoundaryExtension_norm_sq (s : ℂ) (δ : ℝ) (h : 1<2*s.re+δ) :
    ‖primeWeightedBoundaryExtension s δ h‖^2=
      ∑'p : Nat.Primes,(p:ℝ)^(-(2*s.re+δ)) := by
  rw [primeWeightedBoundaryExtension,primeBoundaryExtension_norm_sq]
  apply tsum_congr
  intro p
  congr 1
  simp only [Complex.add_re,Complex.ofReal_re]
  ring

/-- No closed partial linear extension preserves the weighted finite boundary in the critical region. -/
theorem primeWeightedBoundary_no_closed_extension (s : ℂ) (δ : ℝ)
    (h : 2*s.re+δ≤1) (D : Submodule ℂ PrimeChainHilbert) (f : D →ₗ[ℂ] ℂ)
    (hfinite : ∀a,primeWeightedChainEmbedding δ a∈D)
    (hagree : ∀a,f ⟨primeWeightedChainEmbedding δ a,hfinite a⟩=dirichletPrimeChainFunctional s a) :
    ¬IsClosed (Set.range (fun u : D=>(u.val,f u))) := by
  intro hc
  have hsub : primeWeightedBoundaryGraph s δ⊆Set.range (fun u : D=>(u.val,f u)) := by
    rintro z ⟨a,rfl⟩
    exact ⟨⟨primeWeightedChainEmbedding δ a,hfinite a⟩,Prod.ext rfl (hagree a)⟩
  obtain ⟨u,hu⟩:=(closure_minimal hsub hc) (primeWeightedBoundary_graph_closure_unit s δ h)
  have hu0 : u=0 := Subtype.ext (congrArg Prod.fst hu)
  have hh:=congrArg Prod.snd hu
  change f u=1 at hh
  rw [hu0,map_zero] at hh
  exact zero_ne_one hh

/-- Closed extension and bounded extension have the same exact arithmetic half-plane. -/
theorem primeWeightedBoundary_closed_extension_iff (s : ℂ) (δ : ℝ) :
    (∃ (D : Submodule ℂ PrimeChainHilbert) (f : D →ₗ[ℂ] ℂ)
      (hfinite : ∀a,primeWeightedChainEmbedding δ a∈D),
      (∀a,f ⟨primeWeightedChainEmbedding δ a,hfinite a⟩=dirichletPrimeChainFunctional s a) ∧
        IsClosed (Set.range (fun u : D=>(u.val,f u)))) ↔ 1<2*s.re+δ := by
  constructor
  · rintro ⟨D,f,hfinite,hagree,hclosed⟩
    by_contra hn
    exact primeWeightedBoundary_no_closed_extension s δ (le_of_not_gt hn)
      D f hfinite hagree hclosed
  · intro h
    let φ:=primeWeightedBoundaryExtension s δ h
    let D : Submodule ℂ PrimeChainHilbert:=⊤
    let f : D →ₗ[ℂ] ℂ:=φ.toLinearMap.comp D.subtype
    have hfinite (a) : primeWeightedChainEmbedding δ a∈D:=Submodule.mem_top
    refine ⟨D,f,hfinite,?_,?_⟩
    · intro a
      exact LinearMap.congr_fun (primeWeightedBoundaryExtension_finite s δ h) a
    · have he : Set.range (fun u : D=>(u.val,f u))=
          {z : PrimeChainHilbert × ℂ | φ z.1=z.2} := by
        ext z
        constructor
        · rintro ⟨u,rfl⟩
          rfl
        · intro hz
          exact ⟨⟨z.1,Submodule.mem_top⟩,Prod.ext rfl hz⟩
      rw [he]
      exact isClosed_eq (φ.continuous.comp continuous_fst) continuous_snd

#print axioms primeWeightedBoundaryExtension_finite
#print axioms primeWeightedBoundaryExtension_norm_sq
#print axioms primeWeightedBoundary_closed_extension_iff

/-- Finite arithmetic chains are dense in the normalized Hilbert carrier. -/
theorem primeChainHilbertEmbedding_dense : DenseRange primeChainHilbertEmbedding := by
  change Dense ((LinearMap.range primeChainHilbertEmbedding : Submodule ℂ PrimeChainHilbert) :
    Set PrimeChainHilbert)
  rw [Submodule.dense_iff_topologicalClosure_eq_top,primeChainHilbertEmbedding,
    Finsupp.range_linearCombination]
  exact (HilbertSchmidt.lpBasis Nat.Primes).dense_span

/-- Every conductor weight retains the same dense finite-chain range after normalization. -/
theorem primeWeightedChainEmbedding_range (δ : ℝ) :
    Set.range (primeWeightedChainEmbedding δ)=Set.range primeChainHilbertEmbedding := by
  let t : ℂ:=((δ/2:ℝ):ℂ)
  ext u
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨dirichletVertexGauge t a,rfl⟩
  · rintro ⟨a,rfl⟩
    refine ⟨dirichletVertexGauge (-t) a,?_⟩
    change primeChainHilbertEmbedding
      ((dirichletVertexGauge t).comp (dirichletVertexGauge (-t)) a)=_
    rw [dirichletVertexGauge_add,add_neg_cancel,dirichletVertexGauge_zero,LinearMap.id_apply]

theorem primeWeightedChainEmbedding_dense (δ : ℝ) :
    DenseRange (primeWeightedChainEmbedding δ) := by
  change Dense (Set.range (primeWeightedChainEmbedding δ))
  rw [primeWeightedChainEmbedding_range]
  exact primeChainHilbertEmbedding_dense

/-- The arithmetic comparison determines a bounded extension uniquely. -/
theorem primeWeightedBoundaryExtension_unique (s : ℂ) (δ : ℝ) (h : 1<2*s.re+δ)
    (φ : PrimeChainHilbert →L[ℂ] ℂ)
    (hφ : φ.toLinearMap.comp (primeWeightedChainEmbedding δ)=dirichletPrimeChainFunctional s) :
    φ=primeWeightedBoundaryExtension s δ h := by
  apply ContinuousLinearMap.ext
  have he : Set.EqOn φ (primeWeightedBoundaryExtension s δ h)
      (Set.range (primeWeightedChainEmbedding δ)) := by
    rintro u ⟨a,rfl⟩
    exact (LinearMap.congr_fun hφ a).trans
      (LinearMap.congr_fun (primeWeightedBoundaryExtension_finite s δ h) a).symm
  intro u
  exact (closure_minimal he (isClosed_eq φ.continuous
    (primeWeightedBoundaryExtension s δ h).continuous)) (primeWeightedChainEmbedding_dense δ u)

#print axioms primeChainHilbertEmbedding_dense
#print axioms primeWeightedChainEmbedding_dense
#print axioms primeWeightedBoundaryExtension_unique

/-- No finite arithmetic coefficients are lost by the Hilbert embedding. -/
theorem primeChainHilbertEmbedding_injective : Function.Injective primeChainHilbertEmbedding :=
  (HilbertSchmidt.lpBasis Nat.Primes).orthonormal.linearIndependent.finsuppLinearCombination_injective

/-- Conductor normalization preserves every finite arithmetic chain faithfully. -/
theorem primeWeightedChainEmbedding_injective (δ : ℝ) :
    Function.Injective (primeWeightedChainEmbedding δ) := by
  intro a b hab
  apply primeChainHilbertEmbedding_injective at hab
  have he:=congrArg (dirichletVertexGauge (-((δ/2:ℝ):ℂ))) hab
  change ((dirichletVertexGauge (-((δ/2:ℝ):ℂ))).comp
    (dirichletVertexGauge ((δ/2:ℝ):ℂ))) a =
      ((dirichletVertexGauge (-((δ/2:ℝ):ℂ))).comp
        (dirichletVertexGauge ((δ/2:ℝ):ℂ))) b at he
  simpa only [dirichletVertexGauge_add,neg_add_cancel,dirichletVertexGauge_zero,
    LinearMap.id_apply] using he

#print axioms primeWeightedChainEmbedding_injective

end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
