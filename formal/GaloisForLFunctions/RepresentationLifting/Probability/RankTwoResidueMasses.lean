import GaloisForLFunctions.RepresentationLifting.Probability.IrreducibleRankTwoResidues
import GaloisForLFunctions.RepresentationLifting.Probability.PadicMatrixHaar
import Mathlib.Data.Nat.Choose.Cast

/-!
# Spectral branches of a rank-two Haar residue

Lapid and Shusterman, Proposition C.2, separate the irreducible,
distinct-split and repeated-root residue classes before lifting.
The reduction map realizes all three finite-field counts as additive
Haar probabilities at each prime, including two.
-/

namespace GaloisForLFunctions.RepresentationLifting
open MeasureTheory OperatorKernels Matrix
noncomputable section
variable (p : ℕ) [Fact p.Prime]

omit [Fact p.Prime] in
private theorem ambient_precision_card (h : ℕ) :
    Nat.card (Matrix (Fin 2) (Fin 2) (ZMod (p^h)))=(p^h)^4 := by
  simp only [Matrix,Nat.card_fun,Nat.card_fin,Nat.card_zmod,← pow_mul]
  congr 1
  omega

omit [Fact p.Prime] in
private theorem ambient_residue_card :
    Nat.card (Matrix (Fin 2) (Fin 2) (ZMod (p^1))) = p^4 := by
  simpa only [pow_one] using ambient_precision_card p 1

/-- Probability of irreducible reduction. Every matrix lift above this event
has a quadratic characteristic polynomial which stays irreducible modulo p. -/
theorem haar_irreducible_rankTwo_residue :
    (padicMatrixHaar p 2).real {A | Irreducible (padicMatrixProjection p 1 (Fin 2) A).charpoly} =
      ((p:ℝ)-1)^2/(2*(p:ℝ)^2) := by
  letI : Fact (p^1).Prime := ⟨by simpa using (Fact.out : p.Prime)⟩
  have hp : (p:ℝ)≠0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [padicMatrixHaar_residue_probability p 1 2 (fun A => Irreducible A.charpoly),
    card_irreducible_rankTwo,ambient_residue_card]
  simp only [ZMod.card,pow_one,Nat.cast_mul,Nat.cast_sub (Fact.out : p.Prime).one_le,
    Nat.cast_one,Nat.cast_choose_two,Nat.cast_pow]
  field_simp [hp]

/-- Distinct split eigenvalues have larger residue mass than the irreducible
branch because each polynomial has two extra triangular fibre lines. -/
theorem haar_distinct_split_rankTwo_residue :
    (padicMatrixHaar p 2).real {M | let A := padicMatrixProjection p 1 (Fin 2) M
      ∃ u v, u≠v ∧ (A.trace,A.det)=(u+v,u*v)} =
      ((p:ℝ)^2-1)/(2*(p:ℝ)^2) := by
  letI : Fact (p^1).Prime := ⟨by simpa using (Fact.out : p.Prime)⟩
  have hp : (p:ℝ)≠0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [padicMatrixHaar_residue_probability p 1 2 (fun A => ∃ u v, u≠v ∧ (A.trace,A.det)=(u+v,u*v)),
    card_split_distinct_rankTwo,ambient_residue_card]
  simp only [ZMod.card,pow_one,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_choose_two,Nat.cast_pow]
  field_simp [hp]
  ring

/-- The full repeated-root residue branch has mass exactly one over p. -/
theorem haar_repeated_rankTwo_residue :
    (padicMatrixHaar p 2).real {M | let A := padicMatrixProjection p 1 (Fin 2) M
      ∃ u, (A.trace,A.det)=(2*u,u^2)} = 1/(p:ℝ) := by
  letI : Fact (p^1).Prime := ⟨by simpa using (Fact.out : p.Prime)⟩
  have hp : (p:ℝ)≠0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [padicMatrixHaar_residue_probability p 1 2 (fun A => ∃ u, (A.trace,A.det)=(2*u,u^2)),
    card_repeated_rankTwo,ambient_residue_card]
  simp only [ZMod.card,pow_one,Nat.cast_pow]
  field_simp [hp]

/-- Scalar rank-two matrices, with their diagonal entry as parameter. -/
def scalarRankTwo {K : Type*} [Zero K] (u : K) : Matrix (Fin 2) (Fin 2) K := !![u,0;0,u]

private theorem scalar_quadratic_label {K : Type*} [Field K] (u : K) :
    ((scalarRankTwo u).trace,(scalarRankTwo u).det)=(2*u,u^2) := by
  simp only [scalarRankTwo,trace_fin_two_of,det_fin_two_of,zero_mul,sub_zero,two_mul,sq]

private abbrev repeatedLabel {K : Type*} [Field K] (A : Matrix (Fin 2) (Fin 2) K) :=
  ∃ u : K, (A.trace,A.det)=(2*u,u^2)

private abbrev scalarLabel {K : Type*} [Zero K] (A : Matrix (Fin 2) (Fin 2) K) :=
  ∃ u : K, A=scalarRankTwo u

theorem card_scalar_rankTwo (K : Type*) [Zero K] :
    Nat.card {A : Matrix (Fin 2) (Fin 2) K // ∃ u : K, A=scalarRankTwo u} = Nat.card K := by
  let e : K ≃ {A : Matrix (Fin 2) (Fin 2) K // scalarLabel A} :=
    { toFun := fun u => ⟨scalarRankTwo u,u,rfl⟩
      invFun := fun A => A.val 0 0
      left_inv := fun _ => rfl
      right_inv := by rintro ⟨_,u,rfl⟩; rfl }
  exact (Nat.card_congr e).symm

/-- The scalar and nonscalar repeated-root strata have sizes q and q³−q.
Subtracting the repeated eigenvalue gives a nonzero nilpotent matrix in
the second stratum. -/
theorem card_nonscalar_repeated_rankTwo (K : Type*) [Field K] [Fintype K] :
    Nat.card {A : Matrix (Fin 2) (Fin 2) K //
       (∃ u : K, (A.trace,A.det)=(2*u,u^2)) ∧ ¬ ∃ u : K, A=scalarRankTwo u} +
      Fintype.card K = (Fintype.card K)^3 := by
  classical
  let R := {A : Matrix (Fin 2) (Fin 2) K // repeatedLabel A}
  let P (A : R) := scalarLabel A.val
  let a : {A : R // P A} ≃ {A : Matrix (Fin 2) (Fin 2) K // scalarLabel A} :=
    { toFun := fun A => ⟨A.val.val,A.property⟩
      invFun := fun A => ⟨⟨A.val,by
        obtain ⟨u,hu⟩ := A.property
        exact ⟨u,by rw [hu]; exact scalar_quadratic_label u⟩⟩,A.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let b : {A : R // ¬P A} ≃
      {A : Matrix (Fin 2) (Fin 2) K // repeatedLabel A ∧ ¬scalarLabel A} :=
    { toFun := fun A => ⟨A.val.val,A.val.property,A.property⟩
      invFun := fun A => ⟨⟨A.val,A.property.1⟩,A.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h := Nat.card_congr (Equiv.sumCompl P)
  rw [Nat.card_sum,Nat.card_congr a,Nat.card_congr b,card_scalar_rankTwo,Nat.card_eq_fintype_card
    (α:=K),show Nat.card R=(Fintype.card K)^3 from card_repeated_rankTwo K] at h
  exact (Nat.add_comm ..).trans h

/-- The scalar residue stratum has mass p⁻³. Its lifts recur at the next
matrix precision after subtracting a scalar and dividing by p. -/
theorem haar_scalar_rankTwo_residue :
    (padicMatrixHaar p 2).real {M | ∃ u, padicMatrixProjection p 1 (Fin 2) M=scalarRankTwo u} =
      1/(p:ℝ)^3 := by
  letI : Fact (p^1).Prime := ⟨by simpa using (Fact.out : p.Prime)⟩
  have hp : (p:ℝ)≠0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [padicMatrixHaar_residue_probability p 1 2 (fun A => ∃ u, A=scalarRankTwo u),
    card_scalar_rankTwo,ambient_residue_card,Nat.card_zmod,pow_one,Nat.cast_pow]
  field_simp [hp]

/-- The nonscalar repeated-root branch fills the rest of the repeated-root
event and has Haar mass (p²−1)/p³, also in residue characteristic two. -/
theorem haar_nonscalar_repeated_rankTwo_residue :
    (padicMatrixHaar p 2).real {M | let A := padicMatrixProjection p 1 (Fin 2) M
      (∃ u, (A.trace,A.det)=(2*u,u^2)) ∧ ¬ ∃ u, A=scalarRankTwo u} =
      ((p:ℝ)^2-1)/(p:ℝ)^3 := by
  letI : Fact (p^1).Prime := ⟨by simpa using (Fact.out : p.Prime)⟩
  have hp : (p:ℝ)≠0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have h := congrArg (fun z : ℕ => (z:ℝ)) (card_nonscalar_repeated_rankTwo (ZMod (p^1)))
  simp only [Nat.cast_add,Nat.cast_pow,ZMod.card,pow_one] at h
  rw [padicMatrixHaar_residue_probability p 1 2 (fun A => repeatedLabel A ∧ ¬scalarLabel A),
    ambient_residue_card,Nat.cast_pow]
  apply (div_eq_div_iff (pow_ne_zero _ hp) (pow_ne_zero _ hp)).mpr
  linear_combination (p:ℝ)^3*h

private theorem scalarRankTwo_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (u : R) :
    (scalarRankTwo u).map f=scalarRankTwo (f u) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [scalarRankTwo]

/-- Scalar congruence tube of precision h around the center of the
integral matrix algebra. Precision zero includes every matrix. -/
def rankTwoScalarTube (h : ℕ) : Set (Matrix (Fin 2) (Fin 2) ℤ_[p]) :=
  {M | ∃ u, padicMatrixProjection p h (Fin 2) M=scalarRankTwo u}

theorem measurableSet_rankTwoScalarTube (h : ℕ) : MeasurableSet (rankTwoScalarTube p h) := by
  letI : NeZero (p^h) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  exact ((isOpen_discrete {A : Matrix (Fin 2) (Fin 2) (ZMod (p^h)) | ∃ u, A=scalarRankTwo u}).preimage
    (padicMatrixProjection_continuous p h 2)).measurableSet

theorem rankTwoScalarTube_antitone : Antitone (rankTwoScalarTube p) := by
  intro h k hhk M hM
  obtain ⟨u,hu⟩ := hM
  let f := ZMod.castHom (pow_dvd_pow p hhk) (ZMod (p^h))
  have he : (padicMatrixProjection p k (Fin 2) M).map f = padicMatrixProjection p h (Fin 2) M := by
    ext i j
    exact DFunLike.congr_fun (PadicInt.zmod_cast_comp_toZModPow (p:=p) h k hhk) (M i j)
  exact ⟨f u,by rw [←he,hu,scalarRankTwo_map]⟩

/-- All three transverse coordinates must vanish at precision h. Their
exact Haar cost is p⁻³ʰ, even where the residue characteristic is two. -/
theorem haar_rankTwoScalarTube (h : ℕ) :
    (padicMatrixHaar p 2).real (rankTwoScalarTube p h) = 1/((p:ℝ)^h)^3 := by
  letI : NeZero (p^h) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have hp : (p:ℝ)≠0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [rankTwoScalarTube,padicMatrixHaar_residue_probability p h 2 (fun A => ∃ u, A=scalarRankTwo u),
    card_scalar_rankTwo,ambient_precision_card,Nat.card_zmod]
  simp only [Nat.cast_pow]
  field_simp [hp]

/-- First nonscalar digit has a geometric law. The previous scalar digits
place no bias on the probability of leaving the center at the next digit. -/
theorem haar_first_nonscalar_digit (h : ℕ) :
    (padicMatrixHaar p 2).real (rankTwoScalarTube p h \ rankTwoScalarTube p (h+1)) =
      (1-1/(p:ℝ)^3)/((p:ℝ)^h)^3 := by
  have hp : (p:ℝ)≠0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [measureReal_sdiff (rankTwoScalarTube_antitone p (Nat.le_succ h))
    (measurableSet_rankTwoScalarTube p (h+1)),
    haar_rankTwoScalarTube,haar_rankTwoScalarTube,pow_succ (p:ℝ) h]
  have shell (x y : ℝ) (hx : x≠0) (hy : y≠0) :
      1/y^3 - 1/(y*x)^3 = (1-1/x^3)/y^3 := by field_simp
  exact shell p ((p:ℝ)^h) hp (pow_ne_zero _ hp)

/-- The scalar matrices themselves have zero additive Haar measure. -/
theorem haar_rankTwo_scalar_null :
    padicMatrixHaar p 2 {M | ∃ u : ℤ_[p], M=scalarRankTwo u}=0 := by
  apply (measureReal_eq_zero_iff (μ:=padicMatrixHaar p 2)).mp
  apply le_antisymm ?_ measureReal_nonneg
  by_contra! hpos
  obtain ⟨k,hk⟩ := PadicInt.exists_pow_neg_lt p hpos
  have hsub : {M | ∃ u : ℤ_[p], M=scalarRankTwo u} ⊆ rankTwoScalarTube p k := by
    rintro _ ⟨u,rfl⟩
    exact ⟨PadicInt.toZModPow k u,scalarRankTwo_map (PadicInt.toZModPow k) u⟩
  have hle := measureReal_mono (μ:=padicMatrixHaar p 2) hsub
  rw [haar_rankTwoScalarTube] at hle
  have hbase : (1:ℝ)≤p := by exact_mod_cast (Fact.out : p.Prime).one_le
  have hpow : (1:ℝ)≤(p:ℝ)^k := one_le_pow₀ hbase
  have hcube : (p:ℝ)^k ≤ ((p:ℝ)^k)^3 := by
    calc
      _ = ((p:ℝ)^k)^1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hpow (by decide)
  have hlt : 1/(p:ℝ)^k < (padicMatrixHaar p 2).real {M | ∃ u : ℤ_[p], M=scalarRankTwo u} := by
    simpa only [zpow_neg,zpow_natCast,one_div] using hk
  exact hlt.not_ge (hle.trans (one_div_le_one_div_of_le (lt_of_lt_of_le zero_lt_one hpow) hcube))

#print axioms haar_rankTwo_scalar_null

#print axioms haar_rankTwoScalarTube
#print axioms haar_first_nonscalar_digit

#print axioms card_nonscalar_repeated_rankTwo
#print axioms haar_scalar_rankTwo_residue
#print axioms haar_nonscalar_repeated_rankTwo_residue

#print axioms haar_irreducible_rankTwo_residue
#print axioms haar_distinct_split_rankTwo_residue
#print axioms haar_repeated_rankTwo_residue
end
end GaloisForLFunctions.RepresentationLifting
