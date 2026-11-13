/-
Marked reference tuples adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Dictionary.InverseRawDictionary

/-!
# Marked reference tuples

Tuples, assigned and remaining ideals and polynomials of the marked reference; squarefree tuple
products; shifted exponents, padding capacities and source boxes.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid
open Asymptotics
open scoped ContDiff FourierTransform SchwartzMap
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap
open scoped Classical SchwartzMap FourierTransform ContDiff
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical SchwartzMap
open MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace DetectorDictionaryInverseMarkedPadding
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber
open HeckeDetectorCoefficientTransfer InverseInitialPhysicalSlots
open InverseInitialDetectorSource InverseInitialRawDictionary InverseInitialConjugateEnergy
open HeckeDetectorPhysicalSelection  _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve Eisenstein
local notation "O" => Eisenstein.O

def radialMajorant : 𝓢(ℝ,ℂ) :=
  Classical.choose DetectorDictionaryInverseRawRadial.exists_raw_radial_majorant

theorem radialMajorant_compact : HasCompactSupport (radialMajorant : ℝ→ℂ) :=
  (Classical.choose_spec DetectorDictionaryInverseRawRadial.exists_raw_radial_majorant).1

theorem radialMajorant_nonneg (x : ℝ) : 0≤(radialMajorant x).re :=
  (Classical.choose_spec DetectorDictionaryInverseRawRadial.exists_raw_radial_majorant).2.1 x

theorem radialMajorant_one (x : ℝ) (hx : x∈Set.Icc (0:ℝ) 1) : radialMajorant x=1 :=
  (Classical.choose_spec DetectorDictionaryInverseRawRadial.exists_raw_radial_majorant).2.2 x hx

/-- Compact radial support reduces the weighted lattice sum to finitely many points. -/
theorem compact_radial_summable (Φ : 𝓢(ℝ,ℂ))
    (hΦ : HasCompactSupport (Φ : ℝ→ℂ)) (Y : ℝ) (hY : 0< Y) (f : O→ℂ) :
    Summable (fun u : O=> radialWeight Φ Y u*‖f u‖^2) := by
  apply summable_of_hasFiniteSupport
  apply (ProbePhysical.elementWindow_finite_support Φ hΦ Y hY).subset
  intro u hu hz
  apply hu
  change (Φ (‖ringComplex u‖^2/Y)).re*‖f u‖^2=0
  rw [ringComplex_norm_sq_eq_absNorm_span]
  change (Φ (ProbePhysical.elementNorm u/Y)).re*‖f u‖^2=0
  change Φ (ProbePhysical.elementNorm u/Y)=0 at hz
  rw [hz,Complex.zero_re,zero_mul]

theorem radialMajorant_summable (Y : ℝ) (hY : 0< Y) (f : O→ℂ) :
    Summable (fun u : O=> radialWeight radialMajorant Y u*‖f u‖^2) :=
  compact_radial_summable radialMajorant radialMajorant_compact Y hY f

theorem finite_source_le_smoothed {Row : Type*} (rows : Finset Row)
    (row : Row→ O) (hinj : Function.Injective row) (f : O→ℂ)
    (Y : ℝ) (hY : 0< Y)
    (hrows : ∀u∈rows,((Ideal.span {row u}).absNorm:ℝ)≤ Y) :
    (∑u∈rows,‖f (row u)‖^2)≤ smoothedEnergy radialMajorant Y f := by
  have he (u : Row) (hu : u∈rows) :
      ‖f (row u)‖^2=radialWeight radialMajorant Y (row u)*‖f (row u)‖^2 := by
    have hn : ‖ringComplex (row u)‖^2/Y∈Set.Icc (0:ℝ) 1 := by
      refine ⟨div_nonneg (sq_nonneg _) hY.le,?_⟩
      apply (div_le_one hY).mpr
      rw [ringComplex_norm_sq_eq_absNorm_span]
      exact hrows u hu
    simp [radialWeight,radialMajorant_one _ hn]
  calc
    _=∑u∈rows,radialWeight radialMajorant Y (row u)*‖f (row u)‖^2 :=
      Finset.sum_congr rfl he
    _=∑u∈rows.image row,radialWeight radialMajorant Y u*‖f u‖^2 := by
      rw [Finset.sum_image (fun a _ b _ hab=> hinj hab)]
    _≤∑'u : O,radialWeight radialMajorant Y u*‖f u‖^2 :=
      (radialMajorant_summable Y hY f).sum_le_tsum _
        (fun u _=> mul_nonneg (radialMajorant_nonneg _) (sq_nonneg _))
    _=smoothedEnergy radialMajorant Y f := rfl

variable {M : Ideal O} [NeZero M] {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

def selectedSource (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (selected : Finset Slot) (W : ℝ→ℂ) (σ t bW : ℝ) (u : O) : ℂ :=
  ∑p∈Fintype.piFinset (fun s:selected=>
      livePrimes M H (F.profile s) (F.upper s) (U^(F.widths s))),
    (star (∏s:selected,primeProfile (F.profile s) (U^(F.widths s)) (F.external s) (p s))/
      fixedBase F.rowData.η F.rowData.m F.rowData.f (∏s:selected,p s))*
    originalTotalPolynomial
      ((HeckeInverseAmplification.idealsUpTo ⌈U^F.r*bW⌉₊).filter _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve.Supported)
      (∏s:selected,p s) (fixedBase F.rowData.η F.rowData.m F.rowData.f) (fun _=>1)
      (twistedProfile (orientedProfile F.reverse W) σ (orientedFrequency F.reverse t))
      U F.r (∑s:selected,F.widths s) u

omit [NeZero M] in
theorem selectedSource_norm (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (selected : Finset Slot) (W : ℝ→ℂ) (σ t bW : ℝ) (lower : Slot→ℝ)
    (hU : 0< U) (hW : ∀x,W x≠0 → x≤ bW)
    (hV : ∀s∈selected,∀x,F.profile s x≠0 → x∈Set.Icc (lower s) (F.upper s))
    (hlarge : ∀s∈selected,((baseCharacter F.rowData).modulus.absNorm:ℝ)< lower s*U^(F.widths s))
    (u : FreeRow) (hu : u∈F.rows) :
    ‖polynomial (F.family u F.label) true W (U^F.r) σ t*F.physicalProduct selected u‖=
      ‖selectedSource F selected W σ t bW u.val‖ :=
  DetectorDictionaryInverseRawFiberSource.fiber_physical_norm_initial
    F selected W σ t bW lower hU hW hV hlarge u hu

omit [NeZero M] in
theorem selectedSource_summable
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (selected : Finset Slot) (W : ℝ→ℂ) (σ t bW Y : ℝ) (hY : 0< Y) :
    Summable (fun u : O=> radialWeight radialMajorant Y u*
      ‖selectedSource F selected W σ t bW u‖^2) :=
  radialMajorant_summable Y hY _

omit [NeZero M] in
theorem selectedSource_energy
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (selected : Finset Slot) (W : ℝ→ℂ) (σ t bW : ℝ) (lower : Slot→ℝ)
    (hU : 0< U) (hW : ∀x,W x≠0 → x≤ bW)
    (hV : ∀s∈selected,∀x,F.profile s x≠0 → x∈Set.Icc (lower s) (F.upper s))
    (hlarge : ∀s∈selected,((baseCharacter F.rowData).modulus.absNorm:ℝ)< lower s*U^(F.widths s)) :
    (∑u∈F.rows,‖polynomial (F.family u F.label) true W (U^F.r) σ t*
      F.physicalProduct selected u‖^2)=
      ∑u∈F.rows,‖selectedSource F selected W σ t bW u.val‖^2 :=
  DetectorDictionaryInverseRawFiberSource.fiber_physical_energy_initial
    F selected W σ t bW lower hU hW hV hlarge

omit [NeZero M] in
theorem fiber_physical_le_padded_smoothed
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (selected : Finset Slot) (W : ℝ→ℂ) (σ t bW ρ : ℝ) (lower : Slot→ℝ)
    (hU : 1≤ U) (hρ : 0≤ρ) (hW : ∀x,W x≠0 → x≤ bW)
    (hV : ∀s∈selected,∀x,F.profile s x≠0 → x∈Set.Icc (lower s) (F.upper s))
    (hlarge : ∀s∈selected,((baseCharacter F.rowData).modulus.absNorm:ℝ)< lower s*U^(F.widths s)) :
    (∑u∈F.rows,‖polynomial (F.family u F.label) true W (U^F.r) σ t*
      F.physicalProduct selected u‖^2)≤
      smoothedEnergy radialMajorant (U^(1+ρ)) (selectedSource F selected W σ t bW) := by
  have hU0 : 0< U := zero_lt_one.trans_le hU
  have hpad : U≤ U^(1+ρ) := by
    calc
      U=U^(1:ℝ) := (Real.rpow_one U).symm
      _≤ U^(1+ρ) := Real.rpow_le_rpow_of_exponent_le hU (by linarith)
  calc
    _=∑u∈F.rows,‖selectedSource F selected W σ t bW u.val‖^2 := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [selectedSource_norm F selected W σ t bW lower hU0 hW hV hlarge u hu]
    _≤ _ := finite_source_le_smoothed F.rows (fun u : FreeRow=> u.val)
      Subtype.val_injective _ _ (Real.rpow_pos_of_pos hU0 _)
      (fun u hu=>(F.row_norm u hu).trans hpad)

omit [NeZero M] in
theorem fiber_inverse_le_padded_smoothed
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (selected : Finset Slot) (n : ℕ) (σ t ρ : ℝ) (lower : Slot→ℝ)
    (hU : 1≤ U) (hρ : 0≤ρ)
    (hV : ∀s∈selected,∀x,F.profile s x≠0 → x∈Set.Icc (lower s) (F.upper s))
    (hlarge : ∀s∈selected,((baseCharacter F.rowData).modulus.absNorm:ℝ)< lower s*U^(F.widths s)) :
    (∑u∈F.rows,‖polynomial (F.family u F.label) true
      ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile) (U^F.r) σ t*
      F.physicalProduct selected u‖^2)≤
      smoothedEnergy radialMajorant (U^(1+ρ))
        (selectedSource F selected ((HeckeDetectorRowwisePolynomial.logProfile^[n])
          F.inverseProfile) σ t (9/4)) :=
  fiber_physical_le_padded_smoothed F selected _ σ t (9/4) ρ lower hU hρ
    (DetectorDictionaryInverseRawFiberSource.fiber_inverse_log_upper F n) hV hlarge

theorem fixed_padding_margins (r z ρ : ℝ) (hρ : 0≤ρ)
    (hfirst : r+2*z<1) (hsecond : 2*r+8*z<3) :
    r+2*z≤(1+ρ)-ρ ∧ 2*r+8*z≤3*(1+ρ)-3*ρ ∧
      InverseMoment.MarkedMargins (1+ρ) r z ρ := by
  unfold InverseMoment.MarkedMargins
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

omit [NeZero M] in
theorem fiber_padding_margins
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (selected : Finset Slot) (ρ : ℝ) (hρ : 0≤ρ)
    (hfirst : F.r+2*(∑s∈selected,F.widths s)<1)
    (hsecond : 2*F.r+8*(∑s∈selected,F.widths s)<3) :
    F.r+2*(∑s∈selected,F.widths s)≤(1+ρ)-ρ ∧
      2*F.r+8*(∑s∈selected,F.widths s)≤3*(1+ρ)-3*ρ ∧
      InverseMoment.MarkedMargins (1+ρ) F.r (∑s∈selected,F.widths s) ρ :=
  fixed_padding_margins _ _ ρ hρ hfirst hsecond

theorem padded_output_budget (U C ρ loss εm : ℝ) (hU : 1≤ U) (hC : 0≤ C)
    (hbudget : ρ+loss≤εm) : C*U^(1+ρ+loss)≤ C*U^(1+εm) := by
  apply mul_le_mul_of_nonneg_left _ hC
  exact Real.rpow_le_rpow_of_exponent_le hU (by linarith)

end DetectorDictionaryInverseMarkedPadding

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace DetectorDictionaryInverseMarkedReference
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber
open InverseInitialRawDictionary InverseInitialDetectorSource InverseInitialPhysicalSlots
open DetectorDictionaryInverseMarkedPadding
local notation "O"=> Eisenstein.O

def slotCoefficient (data:RowData)(V:ℝ→ℂ)(Y:ℝ)(ζ:ℂ)(P:Ideal O) : ℂ :=
  star (primeProfile V Y ζ P)/fixedBase data.η data.m data.f P

theorem slotCoefficient_character (data:RowData)(V:ℝ→ℂ)(Y:ℝ)(ζ:ℂ)(P:Ideal O) :
    slotCoefficient data V Y ζ P=
      idealCoeff (baseCharacter data).inverse P*star (primeProfile V Y ζ P) := by
  rw [slotCoefficient,HeckeDetectorRelativePrime.idealCoeff_inverse,baseCharacter_coeff,
    div_eq_mul_inv,mul_comm]

theorem tuple_coefficient {ι:Type*}[Fintype ι](data:RowData)
    (V:ι→ℝ→ℂ)(Y:ι→ℝ)(ζ:ι→ℂ)(P:ι→ Ideal O) :
    star (∏i,primeProfile (V i) (Y i) (ζ i) (P i))/
      fixedBase data.η data.m data.f (∏i,P i)=
      ∏i,slotCoefficient data (V i) (Y i) (ζ i) (P i) := by
  simp only [slotCoefficient,star_prod,map_prod,Finset.prod_div_distrib]

def normalizedSlotCoefficient (data:RowData)(V:ℝ→ℂ)(Y:ℝ)(ζ:ℂ)(C:ℝ)(P:Ideal O) : ℂ :=
  slotCoefficient data V Y ζ P/(C:ℂ)

theorem tuple_coefficient_normalized {ι:Type*}[Fintype ι](data:RowData)
    (V:ι→ℝ→ℂ)(Y:ι→ℝ)(ζ:ι→ℂ)(C:ι→ℝ)(hC:∀i,C i≠0)(P:ι→ Ideal O) :
    star (∏i,primeProfile (V i) (Y i) (ζ i) (P i))/
      fixedBase data.η data.m data.f (∏i,P i)=
      (∏i,(C i:ℂ))*∏i,normalizedSlotCoefficient data (V i) (Y i) (ζ i) (C i) (P i) := by
  rw [tuple_coefficient,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [normalizedSlotCoefficient]
  field_simp [hC i]

variable {M:Ideal O}[NeZero M]{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
  {U a ε tstar T allowance:ℝ}{i:ℕ}

omit [NeZero M] in
theorem selectedSource_normalized (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (selected:Finset Slot)(W:ℝ→ℂ)(σ t bW:ℝ)(C:Slot→ℝ)(hC:∀s∈selected,C s≠0)(u:O) :
    selectedSource F selected W σ t bW u=
      (∏s∈selected,(C s:ℂ))*
      ∑p∈Fintype.piFinset (fun s:selected=> livePrimes M H (F.profile s) (F.upper s) (U^(F.widths s))),
        (∏s:selected,normalizedSlotCoefficient F.rowData (F.profile s) (U^(F.widths s))
          (F.external s) (C s) (p s))*
        InverseInitialConjugateEnergy.originalTotalPolynomial
          ((HeckeInverseAmplification.idealsUpTo ⌈U^F.r*bW⌉₊).filter _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve.Supported)
          (∏s:selected,p s) (fixedBase F.rowData.η F.rowData.m F.rowData.f) (fun _=>1)
          (twistedProfile (HeckeDetectorCoefficientTransfer.orientedProfile F.reverse W) σ
            (HeckeDetectorCoefficientTransfer.orientedFrequency F.reverse t))
          U F.r (∑s:selected,F.widths s) u := by
  unfold selectedSource
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [tuple_coefficient_normalized F.rowData (fun s:selected=> F.profile s)
    (fun s:selected=> U^(F.widths s)) (fun s:selected=> F.external s)
    (fun s:selected=> C s) (fun s=> hC s s.property) p]
  rw [Finset.prod_coe_sort selected (fun s=>(C s:ℂ))]
  ring

end DetectorDictionaryInverseMarkedReference

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped Classical BigOperators
namespace DetectorDictionaryInverseMarkedReference
open HeckeFamily  UniqueFactorizationMonoid
open InverseInitialConjugateEnergy InverseInitialPoissonBridge
local notation "O"=> Eisenstein.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

omit [DecidableEq ι] in
theorem tuple_product_squarefree (P:ι→ Ideal O)(hP:∀i,Prime (P i))
    (hinj:Function.Injective P) : Squarefree (∏i,P i) := by
  have hs:∀Q∈Finset.univ.image P,Prime Q := by
    intro Q hQ
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hQ
    exact hP i
  have he:(∏Q∈Finset.univ.image P,Q)=∏i,P i :=
    Finset.prod_image (fun i hi j hj h=> hinj h)
  rw [←he]
  exact InverseInitialExcludedPolynomial.prime_product_squarefree _ hs

omit [DecidableEq ι] in
theorem tuple_product_support (P:ι→ Ideal O)(hP:∀i,Prime (P i))
    (_hinj:Function.Injective P) : primeSupport (∏i,P i)=Finset.univ.image P := by
  have hn:(∏i,P i)≠0:=Finset.prod_ne_zero_iff.mpr (fun i hi=>(hP i).ne_zero)
  ext Q
  rw [primeSupport,Multiset.mem_toFinset,mem_normalizedFactors_iff hn,Finset.mem_image]
  constructor
  · rintro ⟨hQ,hd⟩
    obtain ⟨i,hi,hd⟩:=(hQ.dvd_finsetProd_iff P).mp hd
    have he:Q=P i:=associated_iff_eq.mp (hQ.associated_of_dvd (hP i) hd)
    exact ⟨i,hi,he.symm⟩
  · rintro ⟨i,hi,rfl⟩
    exact ⟨hP i,Finset.dvd_prod_of_mem P hi⟩

omit [DecidableEq ι] in
/-- Divisors of a product of distinct prime ideals correspond to subsets of the slots. -/
theorem tuple_divisors_eq_subsets (P:ι→ Ideal O)(hP:∀i,Prime (P i))
    (hinj:Function.Injective P) :
    idealDivisors (∏i,P i)=Finset.univ.powerset.image (fun J:Finset ι=>∏i∈J,P i) := by
  have hs:=tuple_product_squarefree P hP hinj
  have hf:(idealDivisors (∏i,P i)).filter Squarefree=idealDivisors (∏i,P i) := by
    apply Finset.filter_eq_self.mpr
    intro J hJ
    exact hs.squarefree_of_dvd ((mem_idealDivisors hs.ne_zero).mp hJ)
  rw [←hf,squarefree_divisors_eq_image _ hs.ne_zero,tuple_product_support P hP hinj,
    Finset.powerset_image,Finset.image_image]
  congr 1
  funext J
  exact Finset.prod_image (fun i hi j hj h=> hinj h)

omit [Fintype ι] in
theorem tuple_subset_product_injective (P:ι→ Ideal O)(hP:∀i,Prime (P i))
    (hinj:Function.Injective P) : Function.Injective (fun J:Finset ι=>∏i∈J,P i) := by
  let:∀i,(P i).IsMaximal:=fun i=>(Ideal.isPrime_of_prime (hP i)).isMaximal (hP i).ne_zero
  exact SecondPassArithmetic.primeIdealFamily_product_injective P hinj

theorem sum_tuple_divisors (P:ι→ Ideal O)(hP:∀i,Prime (P i))
    (hinj:Function.Injective P)(f:Ideal O→ℂ) :
    (∑j∈idealDivisors (∏i,P i),f j)=∑J∈Finset.univ.powerset,f (∏i∈J,P i) := by
  rw [tuple_divisors_eq_subsets P hP hinj,Finset.sum_image
    (fun J hJ K hK he=> tuple_subset_product_injective P hP hinj he)]

theorem originalTotal_slot_subsets (S:Finset (Ideal O))
    (P:ι→ Ideal O)(hP:∀i,Prime (P i))(hinj:Function.Injective P)
    (η:Ideal O→*ℂ)(a:Ideal O→ℂ)(W:ℝ→ℂ)(Z r z:ℝ)(hZ:0< Z)(u:O) :
    originalTotalPolynomial S (∏i,P i) η a W Z r z u=
      ∑J∈Finset.univ.powerset,
        originalFixedPolynomial S (∏i,P i) (∏i∈J,P i) η a W Z r z u := by
  rw [originalTotalPolynomial_eq_sectors S (tuple_product_squarefree P hP hinj)
    η a W hZ r z (fun _=>0),sum_tuple_divisors P hP hinj]

end DetectorDictionaryInverseMarkedReference

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped Classical BigOperators
namespace DetectorDictionaryInverseMarkedReference
open HeckeFamily InverseInitialConjugateEnergy InverseInitialPoissonBridge
local notation "O"=> Eisenstein.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

abbrev Tuple (L:ι→ Finset (Ideal O)) := ∀i,↥(L i)
abbrev Assigned (L:ι→ Finset (Ideal O))(J:Finset ι) := ∀i:↥J,↥(L i.val)
abbrev Remaining (L:ι→ Finset (Ideal O))(J:Finset ι) := ∀i:{i:ι // i∉J},↥(L i.val)

def joinTuple (L:ι→ Finset (Ideal O))(J:Finset ι)(x:Assigned L J)(y:Remaining L J) : Tuple L :=
  (Equiv.piEquivPiSubtypeProd (fun i=> i∈J) (fun i=>↥(L i))).symm (x,y)

theorem sum_tuple_split (L:ι→ Finset (Ideal O))(J:Finset ι)(f:Tuple L→ℂ) :
    (∑q:Tuple L,f q)=∑x:Assigned L J,∑y:Remaining L J,f (joinTuple L J x y) := by
  rw [←(Equiv.piEquivPiSubtypeProd (fun i=> i∈J) (fun i=>↥(L i))).symm.sum_comp]
  exact Fintype.sum_prod_type _

theorem sum_tuple_original (L:ι→ Finset (Ideal O))(f:(ι→ Ideal O)→ℂ) :
    (∑q:Tuple L,f (fun i=>(q i).val))=∑q∈Fintype.piFinset L,f q := by
  symm
  apply Finset.sum_bij (fun q hq i=>⟨q i,Fintype.mem_piFinset.mp hq i⟩)
  · intro q hq
    exact Finset.mem_univ _
  · intro q hq r hr he
    funext i
    exact congrArg Subtype.val (congrFun he i)
  · intro q hq
    refine ⟨fun i=>(q i).val,Fintype.mem_piFinset.mpr (fun i=>(q i).property),?_⟩
    funext i
    rfl
  · intro q hq
    rfl

theorem tuple_injective (L:ι→ Finset (Ideal O))
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)(q:Tuple L) :
    Function.Injective (fun i=>(q i).val) := by
  intro i j he
  by_contra hij
  exact Finset.disjoint_left.mp (hdis (Finset.mem_univ i) (Finset.mem_univ j) hij)
    (q i).property (by simpa only [he] using (q j).property)

theorem original_selected_subset_sum (S:Finset (Ideal O))
    (L:ι→ Finset (Ideal O))(hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)(coeff:ι→ Ideal O→ℂ)
    (η:Ideal O→*ℂ)(a:Ideal O→ℂ)(W:ℝ→ℂ)(Z r z:ℝ)(hZ:0< Z)(u:O) :
    (∑q:Tuple L,(∏i,coeff i (q i).val)*
      originalTotalPolynomial S (∏i,(q i).val) η a W Z r z u)=
    ∑J∈Finset.univ.powerset,∑q:Tuple L,(∏i,coeff i (q i).val)*
      originalFixedPolynomial S (∏i,(q i).val) (∏i∈J,(q i).val) η a W Z r z u := by
  calc
    _ = ∑q:Tuple L,∑J∈Finset.univ.powerset,(∏i,coeff i (q i).val)*
        originalFixedPolynomial S (∏i,(q i).val) (∏i∈J,(q i).val) η a W Z r z u := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [originalTotal_slot_subsets S _ (fun i=> hprime i _ (q i).property)
        (tuple_injective L hdis q) η a W Z r z hZ u,Finset.mul_sum]
    _ = _ := Finset.sum_comm

theorem original_selected_grouped (S:Finset (Ideal O))
    (L:ι→ Finset (Ideal O))(hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)(coeff:ι→ Ideal O→ℂ)
    (η:Ideal O→*ℂ)(a:Ideal O→ℂ)(W:ℝ→ℂ)(Z r z:ℝ)(hZ:0< Z)(u:O) :
    (∑q:Tuple L,(∏i,coeff i (q i).val)*
      originalTotalPolynomial S (∏i,(q i).val) η a W Z r z u)=
    ∑J∈Finset.univ.powerset,∑x:Assigned L J,∑y:Remaining L J,
      (∏i,coeff i (joinTuple L J x y i).val)*
        originalFixedPolynomial S (∏i,(joinTuple L J x y i).val)
          (∏i∈J,(joinTuple L J x y i).val) η a W Z r z u := by
  rw [original_selected_subset_sum S L hprime hdis coeff η a W Z r z hZ u]
  apply Finset.sum_congr rfl
  intro J hJ
  exact sum_tuple_split L J _

end DetectorDictionaryInverseMarkedReference

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped Classical BigOperators
namespace DetectorDictionaryInverseMarkedReference
open HeckeFamily InverseInitialConjugateEnergy InverseInitialPoissonBridge InverseInitialOverlap
local notation "O"=> Eisenstein.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

def assignedIdeal (L:ι→ Finset (Ideal O))(J:Finset ι)(x:Assigned L J) : Ideal O :=
  ∏i:↥J,(x i).val

def remainingIdeal (L:ι→ Finset (Ideal O))(J:Finset ι)(y:Remaining L J) : Ideal O :=
  ∏i:{i:ι // i∉J},(y i).val

omit [Fintype ι] in
@[simp] theorem joinTuple_assigned (L:ι→ Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(y:Remaining L J)(i:↥J) : joinTuple L J x y i.val=x i := by
  simp [joinTuple,Equiv.piEquivPiSubtypeProd_symm_apply,i.property]

omit [Fintype ι] in
@[simp] theorem joinTuple_remaining (L:ι→ Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(y:Remaining L J)(i:{i:ι // i∉J}) : joinTuple L J x y i.val=y i := by
  simp [joinTuple,Equiv.piEquivPiSubtypeProd_symm_apply,i.property]

omit [Fintype ι] in
theorem joinTuple_assigned_product (L:ι→ Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(y:Remaining L J) :
    (∏i∈J,(joinTuple L J x y i).val)=assignedIdeal L J x := by
  rw [←Finset.prod_coe_sort J (fun i=>(joinTuple L J x y i).val)]
  simp only [joinTuple_assigned,assignedIdeal]

theorem joinTuple_product (L:ι→ Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(y:Remaining L J) :
    (∏i,(joinTuple L J x y i).val)=assignedIdeal L J x*remainingIdeal L J y := by
  have he := (Fintype.prod_subtype_mul_prod_subtype (fun i=> i∈J)
      (fun i=>(joinTuple L J x y i).val)).symm
  simp only [joinTuple_assigned,joinTuple_remaining] at he
  convert he using 1
  try simp only [assignedIdeal,remainingIdeal]
  congr 2
  ext i
  simp

theorem joinTuple_coefficient_product (L:ι→ Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(y:Remaining L J)(coeff:ι→ Ideal O→ℂ) :
    (∏i,coeff i (joinTuple L J x y i).val)=
      (∏i:↥J,coeff i.val (x i).val)*(∏i:{i:ι // i∉J},coeff i.val (y i).val) := by
  have he := (Fintype.prod_subtype_mul_prod_subtype (fun i=> i∈J)
      (fun i=> coeff i (joinTuple L J x y i).val)).symm
  simp only [joinTuple_assigned,joinTuple_remaining] at he
  convert he using 1
  try simp only [assignedIdeal,remainingIdeal]
  congr 2
  ext i
  simp

omit [Fintype ι] [DecidableEq ι] in
theorem assignedIdeal_ne_zero (L:ι→ Finset (Ideal O))(hprime:∀i,∀P∈L i,Prime P)
    (J:Finset ι)(x:Assigned L J) : assignedIdeal L J x≠0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _hi=>(hprime i.val _ (x i).property).ne_zero)

theorem residual_join (L:ι→ Finset (Ideal O))(hprime:∀i,∀P∈L i,Prime P)
    (J:Finset ι)(x:Assigned L J)(y:Remaining L J) :
    residual (∏i,(joinTuple L J x y i).val) (assignedIdeal L J x)=remainingIdeal L J y := by
  rw [joinTuple_product,InverseInitialOverlap.residual,quotient_mul_cancel (assignedIdeal_ne_zero L hprime J x)]

theorem original_selected_grouped_products (S:Finset (Ideal O))
    (L:ι→ Finset (Ideal O))(hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)(coeff:ι→ Ideal O→ℂ)
    (η:Ideal O→*ℂ)(a:Ideal O→ℂ)(W:ℝ→ℂ)(Z r z:ℝ)(hZ:0< Z)(u:O) :
    (∑q:Tuple L,(∏i,coeff i (q i).val)*
      originalTotalPolynomial S (∏i,(q i).val) η a W Z r z u)=
    ∑J∈Finset.univ.powerset,∑x:Assigned L J,
      (∏i:↥J,coeff i.val (x i).val)*
      ∑y:Remaining L J,(∏i:{i:ι // i∉J},coeff i.val (y i).val)*
        originalFixedPolynomial S (assignedIdeal L J x*remainingIdeal L J y)
          (assignedIdeal L J x) η a W Z r z u := by
  rw [original_selected_grouped S L hprime hdis coeff η a W Z r z hZ u]
  apply Finset.sum_congr rfl
  intro J hJ
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [joinTuple_coefficient_product,joinTuple_product,joinTuple_assigned_product]
  ring

end DetectorDictionaryInverseMarkedReference

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped Classical BigOperators
namespace DetectorDictionaryInverseMarkedReference
open HeckeFamily InverseInitialConjugateEnergy InverseInitialPoissonBridge
open InverseInitialOverlap UniqueFactorizationMonoid Eisenstein CanonicalRowCompletion
local notation "O"=> Eisenstein.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

def remainingResidual (S:Finset (Ideal O))(L:ι→ Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(coeff:ι→ Ideal O→ℂ)(η:Ideal O→*ℂ)(a:Ideal O→ℂ)
    (W:ℝ→ℂ)(Z r z G:ℝ)(u:O) : ℂ :=
  ∑y:Remaining L J,star ((∏i:{i:ι // i∉J},coeff i.val (y i).val)*
    (moebius (remainingIdeal L J y):ℂ))*
    conjugatedResidual S (assignedIdeal L J x*remainingIdeal L J y)
      (assignedIdeal L J x) η a W Z r z G u

theorem assigned_remaining_squarefree (L:ι→ Finset (Ideal O))
    (hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(x:Assigned L J)(y:Remaining L J) :
    Squarefree (assignedIdeal L J x*remainingIdeal L J y) := by
  rw [←joinTuple_product]
  exact tuple_product_squarefree _ (fun i=> hprime i _ (joinTuple L J x y i).property)
    (tuple_injective L hdis _)

theorem assigned_source_eq_remainingResidual (S:Finset (Ideal O))
    (L:ι→ Finset (Ideal O))(hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(x:Assigned L J)(coeff:ι→ Ideal O→ℂ)
    (η:Ideal O→*ℂ)(a:Ideal O→ℂ)(W:ℝ→ℂ)(Z r z G:ℝ)(hZ:0< Z)(u:O) :
    (∑y:Remaining L J,(∏i:{i:ι // i∉J},coeff i.val (y i).val)*
      originalFixedPolynomial S (assignedIdeal L J x*remainingIdeal L J y)
        (assignedIdeal L J x) η a W Z r z u)=
    (moebius (assignedIdeal L J x):ℂ)*(Z^(-G):ℝ)*η (assignedIdeal L J x)^2*
      (idealRowHom u (assignedIdeal L J x))^2*
      star (remainingResidual S L J x coeff η a W Z r z G u) := by
  unfold remainingResidual
  simp only [star_sum,star_mul,star_star,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [originalFixedPolynomial_eq_conjugatedResidual S
    (assigned_remaining_squarefree L hprime hdis J x y) (dvd_mul_right _ _) η a W hZ r z G,
    InverseInitialOverlap.residual,quotient_mul_cancel (assignedIdeal_ne_zero L hprime J x)]
  ring

/-- Split each selected prime tuple into its assigned and remaining factors. -/
theorem original_selected_overlap (S:Finset (Ideal O))
    (L:ι→ Finset (Ideal O))(hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)(coeff:ι→ Ideal O→ℂ)
    (η:Ideal O→*ℂ)(a:Ideal O→ℂ)(W:ℝ→ℂ)(Z r z:ℝ)(G:Finset ι→ℝ)
    (hZ:0< Z)(u:O) :
    (∑q:Tuple L,(∏i,coeff i (q i).val)*
      originalTotalPolynomial S (∏i,(q i).val) η a W Z r z u)=
    ∑J∈Finset.univ.powerset,∑x:Assigned L J,
      (∏i:↥J,coeff i.val (x i).val)*(moebius (assignedIdeal L J x):ℂ)*
      (Z^(-G J):ℝ)*η (assignedIdeal L J x)^2*(idealRowHom u (assignedIdeal L J x))^2*
      star (remainingResidual S L J x coeff η a W Z r z (G J) u) := by
  rw [original_selected_grouped_products S L hprime hdis coeff η a W Z r z hZ u]
  apply Finset.sum_congr rfl
  intro J hJ
  apply Finset.sum_congr rfl
  intro x hx
  rw [assigned_source_eq_remainingResidual S L hprime hdis J x coeff η a W Z r z (G J) hZ u]
  ring

end DetectorDictionaryInverseMarkedReference

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped Classical BigOperators
namespace DetectorDictionaryInverseMarkedReference
open HeckeFamily InverseInitialConjugateEnergy InverseInitialPoissonBridge
open InverseInitialOverlap UniqueFactorizationMonoid Eisenstein
open InverseInitialCommonRatios
local notation "O"=> Eisenstein.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

theorem remaining_injective (L:ι→ Finset (Ideal O))
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(y:Remaining L J) : Function.Injective (fun i=>(y i).val) := by
  intro i j he
  apply Subtype.ext
  by_contra hij
  exact Finset.disjoint_left.mp (hdis (Finset.mem_univ i.val) (Finset.mem_univ j.val) hij)
    (y i).property (by simpa only [he] using (y j).property)

theorem remaining_moebius (L:ι→ Finset (Ideal O))(hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(y:Remaining L J) :
    (moebius (remainingIdeal L J y):ℂ)=(-1:ℂ)^Fintype.card {i:ι // i∉J} := by
  let:∀i:{i:ι // i∉J},((y i).val).IsMaximal:=fun i=>
    (Ideal.isPrime_of_prime (hprime i.val _ (y i).property)).isMaximal
      (hprime i.val _ (y i).property).ne_zero
  simpa only [remainingIdeal,Finset.card_univ] using TruncatedPrincipalPoisson.prime_product_moebius
    (fun i=>(y i).val) (fun i=> hprime i.val _ (y i).property)
    (remaining_injective L hdis J y) Finset.univ

def remainingPolynomial (S:Finset (Ideal O))(L:ι→ Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(coeff:ι→ Ideal O→ℂ)(η:Ideal O→*ℂ)
    (W:ℝ→ℂ)(Z r z G:ℝ)(u:O) : ℂ :=
  ∑y:Remaining L J,(∏i:{i:ι // i∉J},star (coeff i.val (y i).val))*
    residualNormalizedPolynomial S (assignedIdeal L J x*remainingIdeal L J y)
      (assignedIdeal L J x) (conjugateIdealCharacter η) (fun _=>1)
      (fun v=> star (W v)) Z r z G u

/-- The remaining squarefree factors contribute a common Möbius sign. -/
theorem remainingResidual_eq_polynomial (S:Finset (Ideal O))
    (L:ι→ Finset (Ideal O))(hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(x:Assigned L J)(coeff:ι→ Ideal O→ℂ)(η:Ideal O→*ℂ)
    (W:ℝ→ℂ)(Z r z G:ℝ)(u:O) :
    remainingResidual S L J x coeff η (fun _=>1) W Z r z G u=
      (-1:ℂ)^Fintype.card {i:ι // i∉J}*
      remainingPolynomial S L J x coeff η W Z r z G u := by
  unfold remainingResidual remainingPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [remaining_moebius L hprime hdis]
  simp only [star_mul,star_prod,star_pow,star_neg,star_one,conjugatedResidual]
  ring

theorem sum_tuple_pi (L:ι→ Finset (Ideal O))
    (f:(∀i∈(Finset.univ:Finset ι),Ideal O)→ℂ) :
    (∑q:Tuple L,f (fun i _=>(q i).val))=
      ∑q∈(Finset.univ:Finset ι).pi L,f q := by
  symm
  apply Finset.sum_bij (fun q hq i=>⟨q i (Finset.mem_univ i),
    Finset.mem_pi.mp hq i (Finset.mem_univ i)⟩)
  · intro q hq
    exact Finset.mem_univ _
  · intro q hq r hr he
    funext i hi
    exact congrArg Subtype.val (congrFun he i)
  · intro q hq
    refine ⟨fun i _=>(q i).val,Finset.mem_pi.mpr (fun i hi=>(q i).property),?_⟩
    funext i
    rfl
  · intro q hq
    rfl

theorem remainingPolynomial_pi (S:Finset (Ideal O))(L:ι→ Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(coeff:ι→ Ideal O→ℂ)(η:Ideal O→*ℂ)
    (W:ℝ→ℂ)(Z r z G:ℝ)(u:O) :
    remainingPolynomial S L J x coeff η W Z r z G u=
      ∑q∈(Finset.univ:Finset {i:ι // i∉J}).pi (fun i=> L i.val),
        (∏i∈(Finset.univ:Finset {i:ι // i∉J}).attach,
          star (coeff i.val.val (q i.val i.property)))*
        residualNormalizedPolynomial S
          (assignedIdeal L J x*survivingProduct Finset.univ q)
          (assignedIdeal L J x) (conjugateIdealCharacter η) (fun _=>1)
          (fun v=> star (W v)) Z r z G u := by
  rw [←sum_tuple_pi]
  unfold remainingPolynomial
  apply Finset.sum_congr rfl
  intro q hq
  simp only [survivingProduct,remainingIdeal]
  rw [Finset.prod_attach _ (fun i=> star (coeff i.val (q i).val)),
    Finset.prod_attach _ (fun i=>(q i).val)]

end DetectorDictionaryInverseMarkedReference

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped Classical BigOperators
namespace DetectorDictionaryInverseMarkedReference
open HeckeFamily InverseInitialConjugateEnergy InverseInitialPoissonBridge
open UniqueFactorizationMonoid CanonicalRowCompletion _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve
local notation "O"=> Eisenstein.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

def assignedMass (L:ι→ Finset (Ideal O))(J:Finset ι)(x:Assigned L J)
    (coeff:ι→ Ideal O→ℂ)(Z G:ℝ) : ℝ :=
  ‖∏i:↥J,coeff i.val (x i).val‖*Z^(-G)

def assignedTerm (S:Finset (Ideal O))(L:ι→ Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(coeff:ι→ Ideal O→ℂ)(η:Ideal O→*ℂ)
    (W:ℝ→ℂ)(Z r z G:ℝ)(u:O) : ℂ :=
  (∏i:↥J,coeff i.val (x i).val)*(moebius (assignedIdeal L J x):ℂ)*
    (Z^(-G):ℝ)*η (assignedIdeal L J x)^2*(idealRowHom u (assignedIdeal L J x))^2*
    star (remainingResidual S L J x coeff η (fun _=>1) W Z r z G u)

omit [Fintype ι] [DecidableEq ι] in
theorem assignedMass_nonneg (L:ι→ Finset (Ideal O))(J:Finset ι)(x:Assigned L J)
    (coeff:ι→ Ideal O→ℂ)(Z G:ℝ)(hZ:0< Z) : 0≤ assignedMass L J x coeff Z G :=
  mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hZ.le _)

theorem assignedTerm_norm_le (S:Finset (Ideal O))(L:ι→ Finset (Ideal O))
    (hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(x:Assigned L J)(coeff:ι→ Ideal O→ℂ)(η:Ideal O→*ℂ)
    (hj:CanonicalQuadraticSieve.Admissible (assignedIdeal L J x))(hη:‖η (assignedIdeal L J x)‖≤1)
    (W:ℝ→ℂ)(Z r z G:ℝ)(hZ:0< Z)(u:O) :
    ‖assignedTerm S L J x coeff η W Z r z G u‖≤
      assignedMass L J x coeff Z G*‖remainingPolynomial S L J x coeff η W Z r z G u‖ := by
  have hμ:‖(moebius (assignedIdeal L J x):ℂ)‖=1 := by simp [hj.2.1.moebius_eq]
  have hrow:‖idealRowHom u (assignedIdeal L J x)‖^2≤1 := by
    have hh:=admissible_row_four_le_one _ hj u
    nlinarith [sq_nonneg (‖idealRowHom u (assignedIdeal L J x)‖^2-1)]
  have hmass:=assignedMass_nonneg L J x coeff Z G hZ
  have he:‖η (assignedIdeal L J x)‖^2≤1:=pow_le_one₀ (norm_nonneg _) hη
  rw [assignedTerm,remainingResidual_eq_polynomial S L hprime hdis]
  simp only [norm_mul,norm_pow,norm_star,norm_neg,norm_one,one_pow,one_mul,
    hμ,mul_one,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hZ.le (-G))]
  change assignedMass L J x coeff Z G*‖η (assignedIdeal L J x)‖^2*
    ‖idealRowHom u (assignedIdeal L J x)‖^2*
    ‖remainingPolynomial S L J x coeff η W Z r z G u‖≤ _
  calc
    _≤ assignedMass L J x coeff Z G*1*1*
      ‖remainingPolynomial S L J x coeff η W Z r z G u‖ := by
      gcongr
    _=_:=by ring

theorem assignedTerm_energy_le (S:Finset (Ideal O))(L:ι→ Finset (Ideal O))
    (hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(x:Assigned L J)(coeff:ι→ Ideal O→ℂ)(η:Ideal O→*ℂ)
    (hj:CanonicalQuadraticSieve.Admissible (assignedIdeal L J x))(hη:‖η (assignedIdeal L J x)‖≤1)
    (W:ℝ→ℂ)(Z r z G:ℝ)(hZ:0< Z)(rows:Finset O)(w:O→ℝ)(hw:∀u,0≤ w u) :
    (∑u∈rows,w u*‖assignedTerm S L J x coeff η W Z r z G u‖^2)≤
      (assignedMass L J x coeff Z G)^2*
      ∑u∈rows,w u*‖remainingPolynomial S L J x coeff η W Z r z G u‖^2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u hu
  have hh:=mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (assignedTerm_norm_le S L hprime hdis J x coeff η hj hη W Z r z G hZ u) 2)
    (hw u)
  convert hh using 1 <;> first | rfl | ring

theorem assigned_family_energy (S:Finset (Ideal O))(L:ι→ Finset (Ideal O))
    (hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(coeff:ι→ Ideal O→ℂ)(η:Ideal O→*ℂ)
    (hj:∀x:Assigned L J,CanonicalQuadraticSieve.Admissible (assignedIdeal L J x))
    (hη:∀x:Assigned L J,‖η (assignedIdeal L J x)‖≤1)
    (W:ℝ→ℂ)(Z r z G:ℝ)(hZ:0< Z)(rows:Finset O)(w:O→ℝ)(hw:∀u,0≤ w u) :
    (∑u∈rows,w u*‖∑x:Assigned L J,assignedTerm S L J x coeff η W Z r z G u‖^2)≤
      (∑x:Assigned L J,assignedMass L J x coeff Z G*
        Real.sqrt (∑u∈rows,w u*‖remainingPolynomial S L J x coeff η W Z r z G u‖^2))^2 := by
  refine (finite_weighted_triangle Finset.univ rows w hw
    (fun x u=> assignedTerm S L J x coeff η W Z r z G u)).trans ?_
  apply pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _=> Real.sqrt_nonneg _))
  apply Finset.sum_le_sum
  intro x hx
  have hh:=Real.sqrt_le_sqrt (assignedTerm_energy_le S L hprime hdis J x coeff η
    (hj x) (hη x) W Z r z G hZ rows w hw)
  rwa [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (assignedMass_nonneg L J x coeff Z G hZ)] at hh

/-- Weighted triangle bounds reduce the original energy to remaining-polynomial moments. -/
theorem original_energy_of_remaining (S:Finset (Ideal O))(L:ι→ Finset (Ideal O))
    (hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (coeff:ι→ Ideal O→ℂ)(η:Ideal O→*ℂ)
    (hj:∀J:Finset ι,∀x:Assigned L J,CanonicalQuadraticSieve.Admissible (assignedIdeal L J x))
    (hη:∀J:Finset ι,∀x:Assigned L J,‖η (assignedIdeal L J x)‖≤1)
    (W:ℝ→ℂ)(Z r z:ℝ)(G:Finset ι→ℝ)(hZ:0< Z)
    (rows:Finset O)(w:O→ℝ)(hw:∀u,0≤ w u)(E:ℝ)(hE:0≤ E)
    (hres:∀J:Finset ι,∀x:Assigned L J,
      (∑u∈rows,w u*‖remainingPolynomial S L J x coeff η W Z r z (G J) u‖^2)≤ E) :
    (∑u∈rows,w u*‖∑q:Tuple L,(∏i,coeff i (q i).val)*
      originalTotalPolynomial S (∏i,(q i).val) η (fun _=>1) W Z r z u‖^2)≤
      (∑J∈Finset.univ.powerset,∑x:Assigned L J,assignedMass L J x coeff Z (G J))^2*E := by
  have heq (u:O) :
      (∑q:Tuple L,(∏i,coeff i (q i).val)*
        originalTotalPolynomial S (∏i,(q i).val) η (fun _=>1) W Z r z u)=
      ∑J∈Finset.univ.powerset,∑x:Assigned L J,
        assignedTerm S L J x coeff η W Z r z (G J) u :=
    original_selected_overlap S L hprime hdis coeff η (fun _=>1) W Z r z G hZ u
  simp_rw [heq]
  have hroot (J:Finset ι) :
      Real.sqrt (∑u∈rows,w u*‖∑x:Assigned L J,
        assignedTerm S L J x coeff η W Z r z (G J) u‖^2)≤
      (∑x:Assigned L J,assignedMass L J x coeff Z (G J))*Real.sqrt E := by
    have hm:0≤∑x:Assigned L J,assignedMass L J x coeff Z (G J) :=
      Finset.sum_nonneg (fun x _=> assignedMass_nonneg L J x coeff Z (G J) hZ)
    have hb:=assigned_family_energy S L hprime hdis J coeff η (hj J) (hη J)
      W Z r z (G J) hZ rows w hw
    have hc : (∑x:Assigned L J,assignedMass L J x coeff Z (G J)*
        Real.sqrt (∑u∈rows,w u*‖remainingPolynomial S L J x coeff η W Z r z (G J) u‖^2))≤
        (∑x:Assigned L J,assignedMass L J x coeff Z (G J))*Real.sqrt E := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hres J x))
        (assignedMass_nonneg L J x coeff Z (G J) hZ)
    have hn : 0≤∑x:Assigned L J,assignedMass L J x coeff Z (G J)*
        Real.sqrt (∑u∈rows,w u*‖remainingPolynomial S L J x coeff η W Z r z (G J) u‖^2) :=
      Finset.sum_nonneg (fun x _=> mul_nonneg (assignedMass_nonneg L J x coeff Z (G J) hZ) (Real.sqrt_nonneg _))
    have hh:=Real.sqrt_le_sqrt (hb.trans (pow_le_pow_left₀ hn hc 2))
    rwa [Real.sqrt_sq (mul_nonneg hm (Real.sqrt_nonneg E))] at hh
  refine (finite_weighted_triangle Finset.univ.powerset rows w hw
    (fun J u=>∑x:Assigned L J,assignedTerm S L J x coeff η W Z r z (G J) u)).trans ?_
  calc
    _≤(∑J∈Finset.univ.powerset,
        (∑x:Assigned L J,assignedMass L J x coeff Z (G J))*Real.sqrt E)^2 := by
      apply pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _=> Real.sqrt_nonneg _))
      exact Finset.sum_le_sum (fun J _=> hroot J)
    _=_:=by rw [←Finset.sum_mul,mul_pow,Real.sq_sqrt hE]

end DetectorDictionaryInverseMarkedReference

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped Classical BigOperators
namespace DetectorDictionaryInverseMarkedReference
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber
open InverseInitialRawDictionary InverseInitialDetectorSource InverseInitialPhysicalSlots
open DetectorDictionaryInverseMarkedPadding HeckeDetectorCoefficientTransfer
open InverseInitialConjugateEnergy
local notation "O"=> Eisenstein.O
variable {M:Ideal O}[NeZero M]{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
  {U a ε tstar T allowance:ℝ}{i:ℕ}

def fiberLists (F:Fiber M H Label Slot U a ε tstar T allowance i)(selected:Finset Slot)
    (s:selected) : Finset (Ideal O) :=
  livePrimes M H (F.profile s) (F.upper s) (U^(F.widths s))

def fiberCoefficient (F:Fiber M H Label Slot U a ε tstar T allowance i)(s:Slot)
    (P:Ideal O) : ℂ := slotCoefficient F.rowData (F.profile s) (U^(F.widths s)) (F.external s) P

omit [NeZero M] in
theorem fiberLists_prime (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (selected:Finset Slot)(s:selected)(P:Ideal O)(hP:P∈fiberLists F selected s) : Prime P := by
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp hP).1).2.1

omit [NeZero M] in
theorem fiberLists_disjoint (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (selected:Finset Slot)(lower:Slot→ℝ)(hU:0< U)
    (hV:∀s∈selected,∀x,F.profile s x≠0→ x∈Set.Icc (lower s) (F.upper s))
    (hsep:∀s∈selected,∀t∈selected,s≠t→
      F.upper s*U^(F.widths s)< lower t*U^(F.widths t) ∨
      F.upper t*U^(F.widths t)< lower s*U^(F.widths s)) :
    ((Finset.univ:Finset selected):Set selected).PairwiseDisjoint (fiberLists F selected) := by
  intro s hs t ht hst
  apply Finset.disjoint_left.mpr
  intro P hP hQ
  have hp:=livePrime_data M H (F.profile s) (lower s) (F.upper s) (U^(F.widths s))
    (Real.rpow_pos_of_pos hU _) (hV s s.property) P hP
  have hq:=livePrime_data M H (F.profile t) (lower t) (F.upper t) (U^(F.widths t))
    (Real.rpow_pos_of_pos hU _) (hV t t.property) P hQ
  rcases hsep s s.property t t.property (fun he=> hst (Subtype.ext he)) with h|h <;>
    linarith [hp.2.2.1,hp.2.2.2,hq.2.2.1,hq.2.2.2]

omit [NeZero M] in
theorem selectedSource_tuple (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (selected:Finset Slot)(W:ℝ→ℂ)(σ t bW:ℝ)(u:O) :
    selectedSource F selected W σ t bW u=
      ∑q:Tuple (fiberLists F selected),(∏s:selected,fiberCoefficient F s (q s).val)*
        originalTotalPolynomial
          ((HeckeInverseAmplification.idealsUpTo ⌈U^F.r*bW⌉₊).filter _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve.Supported)
          (∏s:selected,(q s).val) (fixedBase F.rowData.η F.rowData.m F.rowData.f) (fun _=>1)
          (twistedProfile (orientedProfile F.reverse W) σ (orientedFrequency F.reverse t))
          U F.r (∑s:selected,F.widths s) u := by
  rw [sum_tuple_original (fiberLists F selected) (fun q=>
    (∏s:selected,fiberCoefficient F s (q s))*originalTotalPolynomial
      ((HeckeInverseAmplification.idealsUpTo ⌈U^F.r*bW⌉₊).filter _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve.Supported)
      (∏s:selected,q s) (fixedBase F.rowData.η F.rowData.m F.rowData.f) (fun _=>1)
      (twistedProfile (orientedProfile F.reverse W) σ (orientedFrequency F.reverse t))
      U F.r (∑s:selected,F.widths s) u)]
  unfold selectedSource
  apply Finset.sum_congr rfl
  intro q hq
  rw [tuple_coefficient]
  rfl

omit [NeZero M] in
theorem selectedSource_overlap (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (selected:Finset Slot)(W:ℝ→ℂ)(σ t bW:ℝ)(hU:0< U)
    (hdis:((Finset.univ:Finset selected):Set selected).PairwiseDisjoint (fiberLists F selected))
    (u:O) :
    selectedSource F selected W σ t bW u=
      ∑J∈(Finset.univ:Finset selected).powerset,∑x:Assigned (fiberLists F selected) J,
        assignedTerm
          ((HeckeInverseAmplification.idealsUpTo ⌈U^F.r*bW⌉₊).filter _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve.Supported)
          (fiberLists F selected) J x (fun s=> fiberCoefficient F s)
          (fixedBase F.rowData.η F.rowData.m F.rowData.f)
          (twistedProfile (orientedProfile F.reverse W) σ (orientedFrequency F.reverse t))
          U F.r (∑s:selected,F.widths s) (∑s∈J,F.widths s) u := by
  rw [selectedSource_tuple]
  exact original_selected_overlap _ (fiberLists F selected) (fiberLists_prime F selected)
    hdis (fun s=> fiberCoefficient F s) _ (fun _=>1) _ U F.r _
    (fun J=>∑s∈J,F.widths s) hU u

omit [NeZero M] in
theorem fiberAssigned_admissible (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (selected:Finset Slot)(lower:Slot→ℝ)(hU:0< U)
    (hV:∀s∈selected,∀x,F.profile s x≠0→ x∈Set.Icc (lower s) (F.upper s))
    (hlarge:∀s∈selected,((baseCharacter F.rowData).modulus.absNorm:ℝ)< lower s*U^(F.widths s))
    (hsep:∀s∈selected,∀t∈selected,s≠t→
      F.upper s*U^(F.widths s)< lower t*U^(F.widths t) ∨
      F.upper t*U^(F.widths t)< lower s*U^(F.widths s))
    (J:Finset selected)(x:Assigned (fiberLists F selected) J) :
    _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve.Admissible (assignedIdeal (fiberLists F selected) J x) := by
  have hdis:=fiberLists_disjoint F selected lower hU hV hsep
  have hp (s:↥J):Prime (x s).val:=fiberLists_prime F selected s.val _ (x s).property
  have hinj:Function.Injective (fun s:↥J=>(x s).val) := by
    intro s t he
    apply Subtype.ext
    by_contra hst
    exact Finset.disjoint_left.mp (hdis (Finset.mem_univ s.val) (Finset.mem_univ t.val) hst)
      (x s).property (by simpa only [he] using (x t).property)
  have hs (s:↥J):_root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve.Supported (x s).val := by
    by_contra hn
    have hd:=livePrime_data M H (F.profile s.val) (lower s.val) (F.upper s.val)
      (U^(F.widths s.val)) (Real.rpow_pos_of_pos hU _) (hV s.val s.val.property)
      (x s).val (x s).property
    exact base_nonzero_prime F.rowData (x s).val (hp s)
      ((hlarge s.val s.val.property).trans_le hd.2.2.1)
      (fixedBase_zero_unsupported F.rowData.η F.rowData.m F.rowData.f
        F.rowData.lambda_dvd F.rowData.two_dvd (x s).val hn)
  have hprod (T:Finset ↥J):_root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve.Supported (∏s∈T,(x s).val) := by
    induction T using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty]
      exact ⟨one_ne_zero,by intro P hP;simp only [UniqueFactorizationMonoid.normalizedFactors_one,Multiset.notMem_zero] at hP⟩
    | @insert s T hsT ih =>
      rw [Finset.prod_insert hsT]
      exact (_root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve.supported_mul_iff _ _).mpr ⟨hs s,ih⟩
  exact ⟨(hprod Finset.univ).1,tuple_product_squarefree _ hp hinj,(hprod Finset.univ).2⟩

omit [NeZero M] in
theorem fiberBase_norm (F:Fiber M H Label Slot U a ε tstar T allowance i)(P:Ideal O) :
    ‖fixedBase F.rowData.η F.rowData.m F.rowData.f P‖≤1 := by
  rw [←baseCharacter_coeff]
  exact idealCoeff_norm_le_one _ _

end DetectorDictionaryInverseMarkedReference

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped Classical BigOperators
namespace DetectorDictionaryInverseMarkedReference
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseInitialDetectorSource
open InverseInitialRawDictionary InverseInitialConjugateEnergy InverseInitialPhysicalSlots
open InverseInitialMarkedDictionary
open DetectorDictionaryInverseRawInitialGates InverseInitialExcludedPeriod
open _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CanonicalRowCompletion
local notation "O"=> Eisenstein.O
variable {ι:Type*}[Fintype ι]

theorem deletedBase_zero_unsupported (data:RowData)(I:Ideal O)(hI:¬Supported I) :
    idealCoeff (deletedBase data) I=0 := by
  unfold deletedBase excluded
  rw [idealCoeff_excludePrimes,baseCharacter_coeff,
    fixedBase_zero_unsupported data.η data.m data.f data.lambda_dvd data.two_dvd I hI]
  split_ifs <;> rfl

theorem deletedBase_eq_of_ne_zero (data:RowData)(I:Ideal O)
    (hI:idealCoeff (deletedBase data) I≠0) :
    idealCoeff (deletedBase data) I=fixedBase data.η data.m data.f I := by
  unfold deletedBase excluded at hI ⊢
  rw [idealCoeff_excludePrimes,baseCharacter_coeff] at hI ⊢
  split_ifs with h
  · rfl
  · exact False.elim (hI (by simp [h]))

def deletedSelectedSource (data:RowData)(M:Ideal O)[NeZero M]
    (H:Subgroup (O⧸M)ˣ)(W:ℝ→ℂ)(V:ι→ℝ→ℂ)
    (Z r σ freq bW:ℝ)(b ell:ι→ℝ)(ζ:ι→ℂ)(u:O) : ℂ :=
  ∑p∈Fintype.piFinset (fun i=> livePrimes M H (V i) (b i) (Z^(ell i))),
    (star (∏i,primeProfile (V i) (Z^(ell i)) (ζ i) (p i))/
      idealCoeff (deletedBase data) (∏i,p i))*
    originalTotalPolynomial
      ((HeckeInverseAmplification.idealsUpTo ⌈Z^r*bW⌉₊).filter Supported)
      (∏i,p i) (idealCoeff (deletedBase data)).toMonoidHom (fun _=>1)
      (twistedProfile W σ freq) Z r (∑i,ell i) u

theorem deleted_physical_slots_norm_initial (data:RowData)(u:NonzeroElement)
    (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)(W:ℝ→ℂ)(V:ι→ℝ→ℂ)
    (Z r σ freq bW:ℝ)(a b ell:ι→ℝ)(ζ:ι→ℂ)(hZ:0< Z)
    (hW:∀x,W x≠0→ x≤ bW)(hV:∀i x,V i x≠0→ x∈Set.Icc (a i) (b i))
    (hlarge:∀i,((deletedBase data).modulus.absNorm:ℝ)< a i*Z^(ell i)) :
    ‖polynomial ((data.character u).excludePrimes (excluded data)
        (reflectionExcludedPrimes_prime (basePeriod data))) true W (Z^r) σ freq*
      (∏i,HeckePrimeRow.canonicalPrimeAmplitude M H u.val (V i) (b i) (Z^(ell i)) (ζ i))‖=
    ‖deletedSelectedSource data M H W V Z r σ freq bW b ell ζ u.val‖ := by
  let L:=fun i=> livePrimes M H (V i) (b i) (Z^(ell i))
  let A:=fun p:ι→ Ideal O=>∏i,primeProfile (V i) (Z^(ell i)) (ζ i) (p i)
  have hn (p:ι→ Ideal O)(hp:p∈Fintype.piFinset L)(_ha:A p≠0):
      idealCoeff (deletedBase data) (∏i,p i)≠0 := by
    rw [map_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    have hd:=livePrime_data M H (V i) (a i) (b i) (Z^(ell i))
      (Real.rpow_pos_of_pos hZ _) (hV i) (p i) (Fintype.mem_piFinset.mp hp i)
    exact HeckeDetectorRelativePrime.idealCoeff_ne_zero_of_coprime _ _ hd.1.ne_zero
      (ProbeRaySlots.prime_coprime_of_norm_gt (deletedBase data) ⟨p i,hd.1⟩
        ((hlarge i).trans_le hd.2.2.1))
  have he:=indexed_conjugate_mark_norm (Fintype.piFinset L) (fun p=>∏i,p i) A
    (idealCoeff (deletedBase data)).toMonoidHom
    ((data.character u).excludePrimes (excluded data) (reflectionExcludedPrimes_prime (basePeriod data)))
    u.val (actual_deleted_row data u) W Z r (∑i,ell i) σ freq hZ
    (HeckeInverseAmplification.idealsUpTo ⌈Z^r*bW⌉₊)
    (finite_source_cover W (Z^r) bW (Real.rpow_pos_of_pos hZ _) hW) hn
  rw [amplitude_product_eq_tuples M H _ _ _ _ _ _ hZ,←mul_assoc]
  change ‖polynomial ((data.character u).excludePrimes (excluded data)
    (reflectionExcludedPrimes_prime (basePeriod data))) true W (Z^r) σ freq*↑(Z^(-(∑i,ell i)/2))*
    (∑p∈Fintype.piFinset L,A p*star (idealRowHom u.val (∏i,p i)))‖=_
  rw [he]
  unfold deletedSelectedSource
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [originalTotal_supported_source _ _ _ (deletedBase_zero_unsupported data)]
  rfl

/-- Removing fixed excluded primes bounds marked moments by finitely many dilated moments. -/
theorem marked_fixed_deletion (data:RowData)(rows:Finset NonzeroElement)
    (W:ℝ→ℂ)(X σ t bW:ℝ)(hX:0< X)(hW:∀x,W x≠0→ x≤ bW)
    (mark:NonzeroElement→ℂ) :
    (∑u∈rows,‖polynomial (data.character u) true W X σ t*mark u‖^2)≤
      ((idealDivisors (∏P∈excluded data,P)).card:ℝ)*
      ∑j∈idealDivisors (∏P∈excluded data,P),∑u∈rows,
        ‖polynomial ((data.character u).excludePrimes (excluded data)
          (reflectionExcludedPrimes_prime (basePeriod data))) true W
          (X/(j.absNorm:ℝ)) σ t*mark u‖^2 := by
  simpa only [one_mul] using InverseInitialExcludedEnergy.marked_family rows data.character
    (excluded data) (reflectionExcludedPrimes_prime (basePeriod data)) W X σ t bW hX hW mark
    (fun _=>1) (fun _ _=> zero_le_one)

end DetectorDictionaryInverseMarkedReference

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped Classical BigOperators
namespace DetectorDictionaryInverseMarkedReference
open HeckeFamily InverseInitialPoissonBridge InverseInitialConjugateEnergy InverseInitialCommonRatios
local notation "O"=> Eisenstein.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

def remainingIndexEquiv (J:Finset ι) : {i:ι // i∉J} ≃ ↥(Finset.univ\J) where
  toFun i:=⟨i.val,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,i.property⟩⟩
  invFun i:=⟨i.val,(Finset.mem_sdiff.mp i.property).2⟩
  left_inv _:=rfl
  right_inv _:=rfl

theorem remaining_product_attach {A:Type*}[CommMonoid A]
    (J:Finset ι)(f:{i:ι // i∉J}→ A) :
    (∏i,f i)=∏i∈(Finset.univ\J).attach,f ⟨i.val,(Finset.mem_sdiff.mp i.property).2⟩ := by
  exact ((remainingIndexEquiv J).symm.prod_comp f).symm

def remainingPi (L:ι→ Finset (Ideal O))(J:Finset ι)(q:Remaining L J) :
    ∀i∈Finset.univ\J,Ideal O := fun i hi=>(q ⟨i,(Finset.mem_sdiff.mp hi).2⟩).val

theorem sum_remaining_original (L:ι→ Finset (Ideal O))(J:Finset ι)
    (f:(∀i∈Finset.univ\J,Ideal O)→ℂ) :
    (∑q:Remaining L J,f (remainingPi L J q))=∑q∈(Finset.univ\J).pi L,f q := by
  symm
  apply Finset.sum_bij (fun q hq i=>⟨q i.val (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,i.property⟩),
    Finset.mem_pi.mp hq i.val (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,i.property⟩)⟩)
  · intro q hq
    exact Finset.mem_univ _
  · intro q hq r hr he
    funext i hi
    exact congrArg Subtype.val (congrFun he ⟨i,(Finset.mem_sdiff.mp hi).2⟩)
  · intro q hq
    refine ⟨remainingPi L J q,Finset.mem_pi.mpr (fun i hi=>(q ⟨i,(Finset.mem_sdiff.mp hi).2⟩).property),?_⟩
    funext i
    rfl
  · intro q hq
    rfl

theorem remainingPolynomial_original_pi (S:Finset (Ideal O))(L:ι→ Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(coeff:ι→ Ideal O→ℂ)(η:Ideal O→*ℂ)
    (W:ℝ→ℂ)(Z r z G:ℝ)(u:O) :
    remainingPolynomial S L J x coeff η W Z r z G u=
      ∑q∈(Finset.univ\J).pi L,(∏i∈(Finset.univ\J).attach,star (coeff i.val (q i.val i.property)))*
        residualNormalizedPolynomial S (assignedIdeal L J x*survivingProduct (Finset.univ\J) q)
          (assignedIdeal L J x) (conjugateIdealCharacter η) (fun _=>1)
          (fun v=> star (W v)) Z r z G u := by
  rw [←sum_remaining_original]
  unfold remainingPolynomial
  apply Finset.sum_congr rfl
  intro q hq
  unfold remainingIdeal survivingProduct remainingPi
  rw [remaining_product_attach J (fun i=> star (coeff i.val (q i).val)),
    remaining_product_attach J (fun i=>(q i).val)]

end DetectorDictionaryInverseMarkedReference

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped Classical BigOperators
namespace DetectorDictionaryInverseMarkedReference
open HeckeFamily _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve InverseInitialCommonRatios InverseInitialExcludedPool
local notation "O"=> Eisenstein.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

theorem tuple_supported (L:ι→ Finset (Ideal O))(hs:∀i,∀P∈L i,Supported P)(q:Tuple L) :
    Supported (∏i,(q i).val) := by
  have hh (T:Finset ι):Supported (∏i∈T,(q i).val) := by
    induction T using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty]
      exact ⟨one_ne_zero,by intro P hP;simp only [UniqueFactorizationMonoid.normalizedFactors_one,Multiset.notMem_zero] at hP⟩
    | @insert i T hi ih =>
      rw [Finset.prod_insert hi]
      exact (supported_mul_iff _ _).mpr ⟨hs i _ (q i).property,ih⟩
  exact hh Finset.univ

theorem tuple_admissible (L:ι→ Finset (Ideal O))(hp:∀i,∀P∈L i,Prime P)
    (hs:∀i,∀P∈L i,Supported P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)(q:Tuple L) :
    CanonicalQuadraticSieve.Admissible (∏i,(q i).val) :=
  ⟨(tuple_supported L hs q).1,tuple_product_squarefree _ (fun i=> hp i _ (q i).property)
    (tuple_injective L hdis q),(tuple_supported L hs q).2⟩

def remainingFromPi (L:ι→ Finset (Ideal O))(J:Finset ι)
    (t:∀i∈Finset.univ\J,Ideal O)(ht:t∈(Finset.univ\J).pi L) : Remaining L J :=
  fun i=>⟨t i.val (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,i.property⟩),
    Finset.mem_pi.mp ht i.val (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,i.property⟩)⟩

theorem remainingIdeal_fromPi (L:ι→ Finset (Ideal O))(J:Finset ι)
    (t:∀i∈Finset.univ\J,Ideal O)(ht:t∈(Finset.univ\J).pi L) :
    remainingIdeal L J (remainingFromPi L J t ht)=survivingProduct (Finset.univ\J) t := by
  unfold remainingIdeal
  rw [remaining_product_attach]
  rfl

theorem remaining_tuple_admissible (L:ι→ Finset (Ideal O))(hp:∀i,∀P∈L i,Prime P)
    (hs:∀i,∀P∈L i,Supported P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(x:Assigned L J)(t:∀i∈Finset.univ\J,Ideal O)
    (ht:t∈(Finset.univ\J).pi L) :
    CanonicalQuadraticSieve.Admissible (assignedIdeal L J x*survivingProduct (Finset.univ\J) t) := by
  rw [←remainingIdeal_fromPi L J t ht,←joinTuple_product]
  exact tuple_admissible L hp hs hdis _

theorem remaining_tuple_coprime (L:ι→ Finset (Ideal O))(hp:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(t:∀i∈Finset.univ\J,Ideal O)(ht:t∈(Finset.univ\J).pi L) :
    Pairwise (Function.onFun IsCoprime (fun i:↥(Finset.univ\J)=> t i.val i.property)) := by
  intro i j hij
  have hiP:=hp i.val _ (Finset.mem_pi.mp ht i.val i.property)
  have hjP:=hp j.val _ (Finset.mem_pi.mp ht j.val j.property)
  let:(t i.val i.property).IsMaximal:=(Ideal.isPrime_of_prime hiP).isMaximal hiP.ne_zero
  let:(t j.val j.property).IsMaximal:=(Ideal.isPrime_of_prime hjP).isMaximal hjP.ne_zero
  apply Ideal.isCoprime_of_isMaximal
  intro he
  dsimp only at he
  exact Finset.disjoint_left.mp (hdis (Finset.mem_univ i.val) (Finset.mem_univ j.val)
    (fun hh=> hij (Subtype.ext hh))) (Finset.mem_pi.mp ht i.val i.property)
      (by rw [he];exact Finset.mem_pi.mp ht j.val j.property)

omit [DecidableEq ι] in
theorem tuple_outside (L:ι→ Finset (Ideal O))(E:Finset (Ideal O))(hE:∀P∈E,Prime P)
    (hout:∀i,∀P∈L i,outside E P)(q:Tuple L) : outside E (∏i,(q i).val) := by
  intro P hP hd
  obtain ⟨i,hi,hdi⟩:=((hE P hP).dvd_finsetProd_iff (fun i=>(q i).val)).mp hd
  exact hout i _ (q i).property P hP hdi

theorem remaining_tuple_outside (L:ι→ Finset (Ideal O))(E:Finset (Ideal O))(hE:∀P∈E,Prime P)
    (hout:∀i,∀P∈L i,outside E P)(J:Finset ι)(x:Assigned L J)
    (t:∀i∈Finset.univ\J,Ideal O)(ht:t∈(Finset.univ\J).pi L) :
    outside E (assignedIdeal L J x*survivingProduct (Finset.univ\J) t) := by
  rw [←remainingIdeal_fromPi L J t ht,←joinTuple_product]
  exact tuple_outside L E hE hout _

end DetectorDictionaryInverseMarkedReference

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace DetectorDictionaryInverseAssignedCount
local notation "O" => Eisenstein.O

def assignedTuples {ι : Type*} [Fintype ι]
    (L : ι → Finset (Ideal O)) : Finset (ι → Ideal O) := Fintype.piFinset L

@[simp] theorem mem_assignedTuples {ι : Type*} [Fintype ι]
    (L : ι → Finset (Ideal O)) (q : ι → Ideal O) :
    q ∈ assignedTuples L ↔ ∀ i, q i ∈ L i := by
  simp [assignedTuples]

def assignedConstant (K : ℕ) (b : ℝ) : ℝ := (128*b)^K

theorem assignedConstant_pos (K : ℕ) {b : ℝ} (hb : 1 ≤ b) :
    0 < assignedConstant K b := by
  unfold assignedConstant
  positivity

theorem list_card_le (L : Finset (Ideal O)) {H : ℝ} (hH : 0 ≤ H)
    (hL : ∀ I ∈ L, I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ H) :
    (L.card : ℝ) ≤ 128*H := by
  apply le_trans (Nat.cast_le.mpr (Finset.card_le_card (t :=
    CenteredMomentSourceMass.idealBall H) ?_))
    (CenteredMomentSourceMass.idealBall_card H hH)
  intro I hI
  exact (CenteredMomentSourceMass.mem_idealBall H I).mpr (hL I hI)

/-- Ideal counting bounds the number of prime-slot assignments after normalization. -/
theorem assigned_card_le (K : ℕ) {b U : ℝ} (hb : 1 ≤ b) (hU : 1 ≤ U)
    {ι : Type*} [Fintype ι] (hK : Fintype.card ι ≤ K)
    (ell : ι → ℝ) (L : ι → Finset (Ideal O))
    (hL : ∀ i I, I ∈ L i → I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ b*U^(ell i)) :
    ((assignedTuples L).card : ℝ) ≤ assignedConstant K b * U^(∑ i, ell i) := by
  have hUp : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hb0 : 0 ≤ b := le_trans zero_le_one hb
  have hbase : 1 ≤ 128*b := by linarith
  simp only [assignedTuples, Fintype.card_piFinset, Nat.cast_prod]
  calc
    (∏ i, ((L i).card : ℝ)) ≤ ∏ i, 128*(b*U^(ell i)) :=
      Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
        (fun i _ => list_card_le (L i) (by positivity) (hL i))
    _ = (128*b)^(Fintype.card ι) * U^(∑ i, ell i) := by
      simp_rw [← mul_assoc]
      rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos hUp]
      simp
    _ ≤ assignedConstant K b * U^(∑ i, ell i) := by
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hbase hK)
        (Real.rpow_nonneg hUp.le _)

def assignedCoefficient {ι : Type*} [Fintype ι]
    (a : ι → Ideal O → ℂ) (q : ι → Ideal O) : ℂ := ∏ i, a i (q i)

theorem assignedCoefficient_norm_le_one {ι : Type*} [Fintype ι]
    (L : ι → Finset (Ideal O)) (a : ι → Ideal O → ℂ)
    (ha : ∀ i I, I ∈ L i → ‖a i I‖ ≤ 1)
    (q : ι → Ideal O) (hq : q ∈ assignedTuples L) :
    ‖assignedCoefficient a q‖ ≤ 1 := by
  rw [assignedCoefficient, norm_prod]
  simpa using Finset.prod_le_prod (fun i _ => norm_nonneg (a i (q i)))
    (fun i _ => ha i (q i) ((mem_assignedTuples L q).mp hq i))

theorem restricted_mass_le (K : ℕ) {b U : ℝ} (hb : 1 ≤ b) (hU : 1 ≤ U)
    {ι : Type*} [Fintype ι] (hK : Fintype.card ι ≤ K)
    (ell : ι → ℝ) (L : ι → Finset (Ideal O))
    (hL : ∀ i I, I ∈ L i → I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ b*U^(ell i))
    (a : ι → Ideal O → ℂ) (ha : ∀ i I, I ∈ L i → ‖a i I‖ ≤ 1)
    (T : Finset (ι → Ideal O)) (hT : T ⊆ assignedTuples L) :
    (∑ q ∈ T, ‖assignedCoefficient a q‖) ≤
      assignedConstant K b * U^(∑ i, ell i) := by
  calc
    (∑ q ∈ T, ‖assignedCoefficient a q‖) ≤ ∑ _q ∈ T, (1 : ℝ) :=
      Finset.sum_le_sum (fun q hq => assignedCoefficient_norm_le_one L a ha q (hT hq))
    _ = (T.card : ℝ) := by simp
    _ ≤ ((assignedTuples L).card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hT)
    _ ≤ _ := assigned_card_le K hb hU hK ell L hL

theorem restricted_normalized_mass_le (K : ℕ) {b U : ℝ} (hb : 1 ≤ b) (hU : 1 ≤ U)
    {ι : Type*} [Fintype ι] (hK : Fintype.card ι ≤ K)
    (ell : ι → ℝ) (L : ι → Finset (Ideal O))
    (hL : ∀ i I, I ∈ L i → I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ b*U^(ell i))
    (a : ι → Ideal O → ℂ) (ha : ∀ i I, I ∈ L i → ‖a i I‖ ≤ 1)
    (T : Finset (ι → Ideal O)) (hT : T ⊆ assignedTuples L) :
    (∑ q ∈ T, ‖assignedCoefficient a q‖) * U^(-(∑ i, ell i)) ≤
      assignedConstant K b := by
  have hUp : 0 < U := lt_of_lt_of_le zero_lt_one hU
  calc
    _ ≤ (assignedConstant K b * U^(∑ i, ell i)) * U^(-(∑ i, ell i)) :=
      mul_le_mul_of_nonneg_right (restricted_mass_le K hb hU hK ell L hL a ha T hT)
        (Real.rpow_nonneg hUp.le _)
    _ = _ := by rw [mul_assoc, ← Real.rpow_add hUp]; simp

theorem restricted_sum_normalized_le (K : ℕ) {b U : ℝ} (hb : 1 ≤ b) (hU : 1 ≤ U)
    {ι : Type*} [Fintype ι] (hK : Fintype.card ι ≤ K)
    (ell : ι → ℝ) (L : ι → Finset (Ideal O))
    (hL : ∀ i I, I ∈ L i → I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ b*U^(ell i))
    (a : ι → Ideal O → ℂ) (ha : ∀ i I, I ∈ L i → ‖a i I‖ ≤ 1)
    (T : Finset (ι → Ideal O)) (hT : T ⊆ assignedTuples L) :
    (∑ q ∈ T, ‖assignedCoefficient a q‖ * U^(-(∑ i, ell i))) ≤
      assignedConstant K b := by
  rw [← Finset.sum_mul]
  exact restricted_normalized_mass_le K hb hU hK ell L hL a ha T hT

theorem slots_normalized_mass_le (K : ℕ) {b U : ℝ} (hb : 1 ≤ b) (hU : 1 ≤ U)
    {σ : Type*} (J : Finset σ) (hJ : J.card ≤ K)
    (ell : σ → ℝ) (L : σ → Finset (Ideal O))
    (hL : ∀ i ∈ J, ∀ I ∈ L i, I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ b*U^(ell i))
    (a : σ → Ideal O → ℂ) (ha : ∀ i ∈ J, ∀ I ∈ L i, ‖a i I‖ ≤ 1)
    (T : Finset (J → Ideal O)) (hT : T ⊆ assignedTuples (fun i : J => L i)) :
    (∑ q ∈ T, ‖assignedCoefficient (fun i : J => a i) q‖) * U^(-(∑ i ∈ J, ell i)) ≤
      assignedConstant K b := by
  simpa only [Finset.sum_coe_sort] using
    restricted_normalized_mass_le K hb hU (by simpa using hJ)
      (fun i : J => ell i) (fun i : J => L i)
      (fun i I hI => hL i i.property I hI) (fun i : J => a i)
      (fun i I hI => ha i i.property I hI) T hT

theorem assigned_sum_normalized_le (K : ℕ) {b U : ℝ} (hb : 1 ≤ b) (hU : 1 ≤ U)
    {ι : Type*} [Fintype ι] (hK : Fintype.card ι ≤ K)
    (ell : ι → ℝ) (L : ι → Finset (Ideal O))
    (hL : ∀ i I, I ∈ L i → I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ b*U^(ell i))
    (a : ι → Ideal O → ℂ) (ha : ∀ i I, I ∈ L i → ‖a i I‖ ≤ 1) :
    (∑ q ∈ assignedTuples L, ‖assignedCoefficient a q‖ * U^(-(∑ i, ell i))) ≤
      assignedConstant K b :=
  restricted_sum_normalized_le K hb hU hK ell L hL a ha _ (Finset.Subset.refl _)

theorem slots_card_le (K : ℕ) {b U : ℝ} (hb : 1 ≤ b) (hU : 1 ≤ U)
    {σ : Type*} (J : Finset σ) (hJ : J.card ≤ K)
    (ell : σ → ℝ) (L : σ → Finset (Ideal O))
    (hL : ∀ i ∈ J, ∀ I ∈ L i, I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ b*U^(ell i)) :
    ((assignedTuples (fun i : J => L i)).card : ℝ) ≤
      assignedConstant K b * U^(∑ i ∈ J, ell i) := by
  simpa only [Finset.sum_coe_sort] using
    assigned_card_le K hb hU (by simpa using hJ)
      (fun i : J => ell i) (fun i : J => L i)
      (fun i I hI => hL i i.property I hI)

theorem assignedTuples_eq_empty {ι : Type*} [Fintype ι]
    (L : ι → Finset (Ideal O)) (i : ι) (hi : L i = ∅) :
    assignedTuples L = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q hq
  have h := (mem_assignedTuples L q).mp hq i
  simp only [hi, Finset.notMem_empty] at h

theorem assignedTuples_card_of_isEmpty {ι : Type*} [Fintype ι] [IsEmpty ι]
    (L : ι → Finset (Ideal O)) : (assignedTuples L).card = 1 := by
  simp [assignedTuples]

end DetectorDictionaryInverseAssignedCount

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped Classical BigOperators
namespace DetectorDictionaryInverseMarkedReference
open HeckeFamily DetectorDictionaryInverseAssignedCount
local notation "O"=> Eisenstein.O

private theorem sum_tuple_real {ι:Type*}[Fintype ι](L:ι→ Finset (Ideal O))
    (f:(ι→ Ideal O)→ℝ) :
    (∑q:Tuple L,f (fun i=>(q i).val))=∑q∈assignedTuples L,f q := by
  symm
  apply Finset.sum_bij (fun q hq i=>⟨q i,(mem_assignedTuples L q).mp hq i⟩)
  · intro q hq
    exact Finset.mem_univ _
  · intro q hq r hr he
    funext i
    exact congrArg Subtype.val (congrFun he i)
  · intro q hq
    refine ⟨fun i=>(q i).val,(mem_assignedTuples L _).mpr (fun i=>(q i).property),?_⟩
    funext i
    rfl
  · intro q hq
    rfl

variable {ι:Type*}[Fintype ι][DecidableEq ι]

omit [Fintype ι] in
theorem assignedMass_sum_le (K:ℕ){b U:ℝ}(hb:1≤ b)(hU:1≤ U)
    (L:ι→ Finset (Ideal O))(J:Finset ι)(hJ:J.card≤ K)(ell:ι→ℝ)
    (hL:∀i∈J,∀P∈L i,P≠0 ∧ (P.absNorm:ℝ)≤ b*U^(ell i))
    (coeff:ι→ Ideal O→ℂ)(hc:∀i∈J,∀P∈L i,‖coeff i P‖≤1) :
    (∑x:Assigned L J,assignedMass L J x coeff U (∑i∈J,ell i))≤ assignedConstant K b := by
  have he:=assigned_sum_normalized_le K hb hU (by simpa using hJ)
    (fun i:↥J=> ell i) (fun i:↥J=> L i)
    (fun i P hP=> hL i i.property P hP)
    (fun i:↥J=> coeff i) (fun i P hP=> hc i i.property P hP)
  rw [←sum_tuple_real] at he
  simp only [assignedMass,assignedCoefficient,Finset.sum_coe_sort] at he ⊢
  convert he using 1
  congr 1
  ext x
  simp

theorem all_assignedMass_sum_le (K:ℕ){b U:ℝ}(hb:1≤ b)(hU:1≤ U)
    (hK:Fintype.card ι≤ K)(L:ι→ Finset (Ideal O))(ell:ι→ℝ)
    (hL:∀i,∀P∈L i,P≠0 ∧ (P.absNorm:ℝ)≤ b*U^(ell i))
    (coeff:ι→ Ideal O→ℂ)(hc:∀i,∀P∈L i,‖coeff i P‖≤1) :
    (∑J∈Finset.univ.powerset,∑x:Assigned L J,assignedMass L J x coeff U (∑i∈J,ell i))≤
      (2:ℝ)^K*assignedConstant K b := by
  calc
    _≤∑J∈(Finset.univ:Finset ι).powerset,assignedConstant K b := by
      apply Finset.sum_le_sum
      intro J hJ
      exact assignedMass_sum_le K hb hU L J ((Finset.card_le_univ J).trans hK) ell
        (fun i _=> hL i) coeff (fun i _=> hc i)
    _=(2:ℝ)^Fintype.card ι*assignedConstant K b := by
      simp
    _≤ _:=mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hK)
      (assignedConstant_pos K hb).le

/-- The normalized assigned mass absorbs the sum over all subsets of slots. -/
theorem original_energy_with_assigned_count (K:ℕ){b U:ℝ}(hb:1≤ b)(hU:1≤ U)
    (hK:Fintype.card ι≤ K)(S:Finset (Ideal O))(L:ι→ Finset (Ideal O))
    (hp:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)(ell:ι→ℝ)
    (hL:∀i,∀P∈L i,P≠0 ∧ (P.absNorm:ℝ)≤ b*U^(ell i))
    (coeff:ι→ Ideal O→ℂ)(hc:∀i,∀P∈L i,‖coeff i P‖≤1)(η:Ideal O→*ℂ)
    (hj:∀J:Finset ι,∀x:Assigned L J,_root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve.Admissible (assignedIdeal L J x))
    (hη:∀J:Finset ι,∀x:Assigned L J,‖η (assignedIdeal L J x)‖≤1)
    (W:ℝ→ℂ)(r z:ℝ)(rows:Finset O)(w:O→ℝ)(hw:∀u,0≤ w u)(E:ℝ)(hE:0≤ E)
    (hres:∀J:Finset ι,∀x:Assigned L J,
      (∑u∈rows,w u*‖remainingPolynomial S L J x coeff η W U r z (∑i∈J,ell i) u‖^2)≤ E) :
    (∑u∈rows,w u*‖∑q:Tuple L,(∏i,coeff i (q i).val)*
      InverseInitialConjugateEnergy.originalTotalPolynomial S (∏i,(q i).val) η (fun _=>1) W U r z u‖^2)≤
      ((2:ℝ)^K*assignedConstant K b)^2*E := by
  have hU0:0< U:=zero_lt_one.trans_le hU
  refine (original_energy_of_remaining S L hp hdis coeff η hj hη W U r z
    (fun J=>∑i∈J,ell i) hU0 rows w hw E hE hres).trans ?_
  apply mul_le_mul_of_nonneg_right _ hE
  apply pow_le_pow_left₀
    (Finset.sum_nonneg (fun J _=> Finset.sum_nonneg
      (fun x _=> assignedMass_nonneg L J x coeff U (∑i∈J,ell i) hU0)))
  exact all_assignedMass_sum_le K hb hU hK L ell hL coeff hc

end DetectorDictionaryInverseMarkedReference

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped Classical BigOperators Topology
namespace DetectorDictionaryInverseMarkedReference
open HeckeFamily HeckeInverseAmplification Filter 
open DetectorDictionaryInverseRawInitialGates
local notation "O"=> Eisenstein.O

def shiftedExponent (_data:RowData)(U r:ℝ)(j:Ideal O) : ℝ :=
  r-Real.logb U (j.absNorm:ℝ)

/-- Each fixed excluded divisor changes the scale exponent by a uniformly vanishing amount. -/
theorem marked_shift_eventually (data:RowData)(eta:ℝ)(heta:0< eta) :
    ∀ᶠU:ℝ in atTop,1< U ∧
      ∀j∈idealDivisors (∏P∈excluded data,P),∀r:ℝ,
        r-eta≤ shiftedExponent data U r j ∧ shiftedExponent data U r j≤ r ∧
        U^(shiftedExponent data U r j)=U^r/(j.absNorm:ℝ) := by
  have ht:∀ᶠU:ℝ in atTop,((∏P∈excluded data,P).absNorm:ℝ)≤ U^eta :=
    (tendsto_rpow_atTop heta).eventually (eventually_ge_atTop _)
  filter_upwards [eventually_gt_atTop (1:ℝ),ht] with U hU ht
  refine ⟨hU,?_⟩
  intro j hj r
  obtain ⟨hn,hnB⟩:=excluded_divisor_norm data j hj
  have hU0:0< U:=zero_lt_one.trans hU
  have hn0:0<(j.absNorm:ℝ):=zero_lt_one.trans_le hn
  have hl0:0≤ Real.logb U (j.absNorm:ℝ):=
    div_nonneg (Real.log_nonneg hn) (Real.log_pos hU).le
  have hl:Real.logb U (j.absNorm:ℝ)≤ eta:=
    (Real.logb_le_iff_le_rpow hU hn0).mpr (hnB.trans ht)
  refine ⟨by dsimp [shiftedExponent];linarith,by dsimp [shiftedExponent];linarith,?_⟩
  rw [shiftedExponent,Real.rpow_sub hU0,Real.rpow_logb hU0 hU.ne' hn0]

theorem shifted_padding_capacities (r r' ell ρ gap eta:ℝ)
    (hr:0≤ r)(hell:0≤ ell)(hshift:r-eta≤ r')(hshiftup:r'≤ r)
    (hfirst:r+2*ell<1)(hsecond:2*r+8*ell<3)
    (hgap:2*gap≤ρ)(hgap₃:2*gap≤3*ρ) :
    -eta≤ r' ∧ r'+2*ell≤(1+ρ)-2*gap ∧
      2*r'+8*ell≤3*(1+ρ)-2*gap ∧ r'+ell<1 := by
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem shifted_source_box (r r' ell G eta:ℝ)(hr:0≤ r)(hell:0≤ ell)
    (_hG:0≤ G)(hGell:G≤ ell)(hshift:r-eta≤ r')(hshiftup:r'≤ r)
    (hfirst:r+2*ell<1)(_heta:0≤ eta)(hetaSmall:eta≤1/7) :
    -2≤ r'+ell-2*G ∧ r'+ell+7*eta≤2 := by
  constructor <;> linarith

end DetectorDictionaryInverseMarkedReference

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped Classical BigOperators
namespace InverseInitialMarkedAssignedGeometry
open HeckeFamily 
open DetectorDictionaryInverseMarkedReference InverseInitialQuotientGeometry
local notation "O"=> Eisenstein.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

 def assignedGenerator (L:ι→ Finset (Ideal O))(J:Finset ι)(x:Assigned L J)(i:ι):O:=
  if h:i∈J then cubicIdealGenerator (x ⟨i,h⟩).val else 1

omit [Fintype ι] in
 theorem assignedGenerator_mem (L:ι→ Finset (Ideal O))(J:Finset ι)(x:Assigned L J)
    (i:ι)(hi:i∈J):assignedGenerator L J x i=cubicIdealGenerator (x ⟨i,hi⟩).val:=by
  simp only [assignedGenerator,dif_pos hi]

omit [Fintype ι] in
 theorem assignedGenerator_span (L:ι→ Finset (Ideal O))(J:Finset ι)(x:Assigned L J)
    (i:ι)(hi:i∈J):Ideal.span {assignedGenerator L J x i}=(x ⟨i,hi⟩).val:=by
  rw [assignedGenerator_mem L J x i hi,span_cubicIdealGenerator]

omit [Fintype ι] in
 theorem assignedGenerator_ne_zero (L:ι→ Finset (Ideal O))(J:Finset ι)(x:Assigned L J)
    (hne:∀i∈J,∀P∈L i,P≠0)(i:ι)(hi:i∈J):assignedGenerator L J x i≠0:=by
  rw [assignedGenerator_mem L J x i hi]
  exact cubicIdealGenerator_ne_zero _ (hne i hi _ (x ⟨i,hi⟩).property)

omit [Fintype ι] in
 theorem assignedElement_span (L:ι→ Finset (Ideal O))(J:Finset ι)(x:Assigned L J):
    Ideal.span {assignedElement J (assignedGenerator L J x)}=assignedIdeal L J x:=by
  rw [assignedElement,SchwartzPlanePoisson.span_finset_prime_product,←Finset.prod_coe_sort]
  unfold assignedIdeal
  apply Finset.prod_congr rfl
  intro i hi
  exact assignedGenerator_span L J x i.val i.property

omit [Fintype ι] in
 theorem assignedGenerator_window_live (L:ι→ Finset (Ideal O))(J:Finset ι)(x:Assigned L J)
    (U:ℝ)(ell:ι→ℝ)(W:ι→ℝ→ℂ)
    (hW:∀i∈J,∀P∈L i,W i ((P.absNorm:ℝ)/U^(ell i))≠0):
    ∀i∈J,W i ((Ideal.absNorm (Ideal.span {assignedGenerator L J x i}):ℝ)/U^(ell i))≠0:=by
  intro i hi
  rw [assignedGenerator_span L J x i hi]
  exact hW i hi _ (x ⟨i,hi⟩).property

omit [Fintype ι] [DecidableEq ι] in
 theorem assigned_ratio_product (L:ι→ Finset (Ideal O))(J:Finset ι)(x:Assigned L J)
    (U:ℝ)(hU:0< U)(ell:ι→ℝ):
    (Ideal.absNorm (assignedIdeal L J x):ℝ)/U^(assignedCenter J ell)=
      ∏i:↥J,((x i).val.absNorm:ℝ)/U^(ell i.val):=by
  simp only [assignedIdeal,map_prod,Nat.cast_prod,Finset.prod_div_distrib,
    ←Real.rpow_sum_of_pos hU,Finset.sum_coe_sort,assignedCenter]

omit [Fintype ι] [DecidableEq ι] in
 theorem assigned_ratio_interval (L:ι→ Finset (Ideal O))(J:Finset ι)(x:Assigned L J)
    (U:ℝ)(hU:0< U)(ell:ι→ℝ)(K:ℕ)(hK:J.card≤ K)
    (hL:∀i∈J,∀P∈L i,((P.absNorm:ℝ)/U^(ell i))∈Set.Icc (1:ℝ) 2):
    ((Ideal.absNorm (assignedIdeal L J x):ℝ)/U^(assignedCenter J ell))∈Set.Icc (1:ℝ) ((2:ℝ)^K):=by
  rw [assigned_ratio_product L J x U hU ell]
  constructor
  · have hh:=Finset.prod_le_prod (s:=Finset.univ)
      (f:=fun _i:↥J=>(1:ℝ)) (g:=fun i=>((x i).val.absNorm:ℝ)/U^(ell i.val))
      (fun _ _=> zero_le_one) (fun i _=>(hL i.val i.property _ (x i).property).1)
    simpa only [Finset.prod_const_one] using hh
  · calc
      _≤∏_i:↥J,(2:ℝ):=Finset.prod_le_prod
        (fun i _=>(zero_le_one.trans (hL i.val i.property _ (x i).property).1))
        (fun i _=>(hL i.val i.property _ (x i).property).2)
      _=(2:ℝ)^J.card:=by simp
      _≤(2:ℝ)^K:=pow_le_pow_right₀ (by norm_num) hK

end InverseInitialMarkedAssignedGeometry

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
