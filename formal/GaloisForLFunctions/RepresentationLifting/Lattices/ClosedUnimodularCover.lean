import GaloisForLFunctions.RepresentationLifting.Lattices.PrimeStellarReplacement
import GaloisForLFunctions.HTGeometry.Lattices.ClosedStellarCones
import GaloisForLFunctions.HTGeometry.DualZLatticeCovolume

/-!
# Closed unimodular covers of integral simplicial cones

A modular relation supplies a ray on a support face. Each child has
smaller determinant, and every integral point in a unimodular leaf has
unique nonnegative integral coordinates.
-/

namespace GaloisForLFunctions.RepresentationLifting
open Matrix Module Finset HTGeometry
open scoped Classical NNReal
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The closed real cone spanned by the integer columns. -/
def latticeCone (A : Matrix ι ι ℤ) : Set (ι → ℝ) :=
  PointedCone.hull ℝ (Set.range fun i j => (A j i:ℝ))

private theorem column_basis (A : Matrix ι ι ℤ) (ha : A.det ≠ 0) :
    ∃ b : Basis ι ℝ (ι → ℝ), ∀ i j, b i j = (A j i:ℝ) := by
  let M := (Int.castRingHom ℝ).mapMatrix A
  have hd : IsUnit M.transpose.det := by
    rw [det_transpose,show M.det = (A.det:ℝ) from ((Int.castRingHom ℝ).map_det A).symm]
    exact isUnit_iff_ne_zero.mpr (Int.cast_ne_zero.mpr ha)
  refine ⟨DualZLattice.rowBasis M.transpose hd,fun i j => ?_⟩
  exact congrFun (congrFun (DualZLattice.coe_rowBasis M.transpose hd) i) j

private theorem real_cone_step (A : Matrix ι ι ℤ) (ha : A.det ≠ 0) (w : ι → ℤ) (a : ι → ℝ)
    (hp : ∀ i, 0 ≤ a i) (hpos : ∃ i, 0 < a i)
    (hcast : ∀ j, ∑ i, a i*(A j i:ℝ) = (w j:ℝ)) :
    latticeCone A = ⋃ i : {i // 0 < a i}, latticeCone (A.updateCol i.val w) := by
  obtain ⟨b,hb⟩ := column_basis A ha
  have he : b.equivFun.symm a = fun j => (w j:ℝ) := by
    rw [← b.sum_equivFun (b.equivFun.symm a)]
    funext j
    simpa only [LinearEquiv.apply_symm_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,hb] using hcast j
  have hc : latticeCone A = (lotzBasisCone b : Set (ι → ℝ)) := by
    rw [lotzBasisCone_eq_hull]
    exact congrArg (fun f : ι → ι → ℝ => (PointedCone.hull ℝ (Set.range f) : Set (ι → ℝ)))
      (funext fun i => funext fun j => (hb i j).symm)
  rw [hc,stellarFaceChild_cover b a hp hpos]
  apply Set.iUnion_congr
  intro i
  apply congrArg (fun f : ι → ι → ℝ => (PointedCone.hull ℝ (Set.range f) : Set (ι → ℝ)))
  funext k j
  by_cases hk : k=i.val <;> simp [stellarFaceGenerator,he,hb,hk]

private theorem nonunit_step (A : Matrix ι ι ℤ) (ha : 1 < A.det.natAbs) :
    ∃ (S : Finset ι) (w : ι → ℤ),
      (∀ i ∈ S, 0 < (A.updateCol i w).det.natAbs ∧ (A.updateCol i w).det.natAbs < A.det.natAbs) ∧
      latticeCone A = ⋃ i : S, latticeCone (A.updateCol i.val w) := by
  let p := A.det.natAbs.minFac
  haveI : Fact p.Prime := ⟨Nat.minFac_prime (by omega)⟩
  have hA : A.det ≠ 0 := Int.natAbs_pos.mp (by omega)
  have hdiv : (p:ℤ) ∣ A.det := by
    apply Int.natAbs_dvd_natAbs.mp
    simpa only [Int.natAbs_natCast] using Nat.minFac_dvd A.det.natAbs
  obtain ⟨c,w,k,hn,_,hc,hdet⟩ := prime_stellar_replacement p A hA hdiv
  let a (i : ι) : ℝ := (c i).val/(p:ℝ)^(k+1)
  let S := univ.filter fun i => (c i).val ≠ 0
  have hp : 0 < (p:ℝ)^(k+1) := pow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
  have hpos (i : ι) : 0 < a i ↔ i ∈ S := by
    simp only [a,lt_div_iff₀ hp,zero_mul,S,mem_filter,mem_univ,true_and]
    exact_mod_cast (Nat.pos_iff_ne_zero (n:=(c i).val))
  have hadd (j : ι) : ∑ i, a i*(A j i:ℝ) = (w j:ℝ) := by
    have h := congrArg (fun v : ι → ℤ => (v j:ℝ)) hc
    change (↑(∑ i, A j i * ((c i).val:ℤ)) : ℝ) = ↑((p:ℤ)^(k+1)*w j) at h
    push_cast at h
    have ha' (i : ι) : a i*(A j i:ℝ) = (A j i:ℝ)*(c i).val/(p:ℝ)^(k+1) := by
      unfold a
      ring
    simp_rw [ha']
    rw [← sum_div,div_eq_iff hp.ne',h,mul_comm]
  obtain ⟨i,hi⟩ := hn
  have hne : ∃ i, 0 < a i := ⟨i,(hpos _).mpr (mem_filter.mpr ⟨mem_univ _,hi⟩)⟩
  refine ⟨S,w,fun j hj => (hdet j).2 ((mem_filter.mp hj).2),?_⟩
  rw [real_cone_step A hA w a (fun j => div_nonneg (Nat.cast_nonneg _) hp.le) hne hadd]
  ext y
  simp only [Set.mem_iUnion,Subtype.exists]
  apply exists_congr
  intro j
  rw [hpos j]

private theorem union_children {α β γ : Type*} [Fintype α] [DecidableEq β]
    (L : α → Finset β) (C : β → Set γ) :
    (⋃ i, ⋃ B ∈ L i, C B) = ⋃ B ∈ univ.biUnion L, C B := by
  ext x
  simp only [Set.mem_iUnion,mem_biUnion,mem_univ,true_and]
  constructor
  · rintro ⟨i,B,hB,hx⟩
    exact ⟨B,⟨i,hB⟩,hx⟩
  · rintro ⟨B,⟨i,hB⟩,hx⟩
    exact ⟨i,B,hB,hx⟩

/-- Every nonsingular integral simplicial cone admits a finite cover by closed
unimodular cones. The witness consists of actual integer column matrices. -/
theorem latticeCone_unimodular_cover (A : {M : Matrix ι ι ℤ // M.det ≠ 0}) :
    ∃ L : Finset (Matrix ι ι ℤ), (∀ B ∈ L, B.det.natAbs=1) ∧
      latticeCone A.val = ⋃ B ∈ L, latticeCone B := by
  have go (D : ℕ) (M : Matrix ι ι ℤ) (hD : M.det.natAbs = D) (hpos : 0<D) :
      ∃ L : Finset (Matrix ι ι ℤ), (∀ B ∈ L, B.det.natAbs=1) ∧
        latticeCone M = ⋃ B ∈ L, latticeCone B := by
    induction D using Nat.strong_induction_on generalizing M with
    | h D ih =>
      by_cases hunit : D=1
      · exact ⟨{M},fun B hB => (mem_singleton.mp hB) ▸ hD.trans hunit,by simp⟩
      obtain ⟨S,w,hd,hcov⟩ := nonunit_step M (by omega)
      have hchild (i : S) := ih _ ((hd i.val i.property).2.trans_eq hD)
        (M.updateCol i.val w) rfl (hd i.val i.property).1
      choose L hL hC using hchild
      refine ⟨univ.biUnion L,?_,?_⟩
      · intro B hB
        obtain ⟨i,_,hi⟩ := mem_biUnion.mp hB
        exact hL i B hi
      · rw [hcov]
        exact (Set.iUnion_congr fun i => hC i).trans (union_children L latticeCone)
  exact go _ A.val rfl (Int.natAbs_pos.mpr A.property)

private theorem latticeCone_mem (A : Matrix ι ι ℤ) (x : ι → ℝ) :
    x ∈ latticeCone A ↔ ∃ a : ι → ℝ, (∀ i, 0 ≤ a i) ∧ ((Int.castRingHom ℝ).mapMatrix A) *ᵥ a = x := by
  change x ∈ Submodule.span ℝ≥0 (Set.range fun i j => (A j i:ℝ)) ↔ _
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c,hc⟩
    refine ⟨fun i => (c i).val,fun i => (c i).property,?_⟩
    funext j
    change (∑ i, (A j i:ℝ)*(c i:ℝ)) = x j
    simpa only [Finset.sum_apply,NNReal.smul_def,Pi.smul_apply,smul_eq_mul,mul_comm] using congrFun hc j
  · rintro ⟨a,ha,hx⟩
    refine ⟨fun i => ⟨a i,ha i⟩,?_⟩
    funext j
    have hj : (∑ i, (A j i:ℝ)*a i) = x j := congrFun hx j
    simp only [Finset.sum_apply,NNReal.smul_def,Pi.smul_apply,smul_eq_mul]
    change (∑ i, a i*(A j i:ℝ)) = x j
    simpa only [mul_comm] using hj

private theorem cast_mulVec (A : Matrix ι ι ℤ) (v : ι → ℤ) :
    ((Int.castRingHom ℝ).mapMatrix A) *ᵥ (fun j => (v j:ℝ)) = fun j => ((A *ᵥ v) j:ℝ) :=
  funext fun j => ((Int.castRingHom ℝ).map_mulVec A v j).symm

/-- Each unimodular leaf gives a unique nonnegative integer address for
each of its lattice points. This holds on its boundary as well. -/
theorem unimodularCone_address (A : {M : Matrix ι ι ℤ // M.det.natAbs=1}) (x : ι → ℤ) :
    (fun i => (x i:ℝ)) ∈ latticeCone A.val ↔
      ∃! c : ι → ℕ, A.val *ᵥ (fun i => (c i:ℤ)) = x := by
  let B := A.val
  have hB : IsUnit B.det := Int.isUnit_iff_natAbs_eq.mpr A.property
  let z := B⁻¹ *ᵥ x
  have hz : B *ᵥ z = x := by rw [show B *ᵥ z = (B*B⁻¹) *ᵥ x from mulVec_mulVec _ _ _,mul_nonsing_inv B hB,one_mulVec]
  have uniqueInt (c : ι → ℤ) (hc : B *ᵥ c = x) : c = z := by
    calc
      c = (B⁻¹*B) *ᵥ c := by rw [nonsing_inv_mul B hB,one_mulVec]
      _ = B⁻¹ *ᵥ x := by rw [← mulVec_mulVec,hc]
  rw [latticeCone_mem]
  constructor
  · rintro ⟨a,ha,he⟩
    let R := (Int.castRingHom ℝ).mapMatrix B
    have hR : IsUnit R.det := ((Int.castRingHom ℝ).map_det B) ▸ hB.map _
    have hinj : Function.Injective R.mulVec := (R.toLinearEquiv' (invertibleOfIsUnitDet R hR)).injective
    have hza : (fun j => (z j:ℝ)) = a := hinj (by rw [cast_mulVec,hz]; exact he.symm)
    have hnonneg (i : ι) : 0 ≤ z i := by
      exact_mod_cast ((congrFun hza i).symm ▸ ha i)
    let c (i : ι) := (z i).toNat
    have hc : (fun i => (c i:ℤ)) = z := funext fun i => Int.toNat_of_nonneg (hnonneg i)
    refine ⟨c,?_,?_⟩
    · change B *ᵥ (fun i => (c i:ℤ)) = x
      rw [hc,hz]
    intro d hd
    have hh := (uniqueInt _ hd).trans hc.symm
    exact funext fun i => Int.ofNat_inj.mp (congrFun hh i)
  · rintro ⟨c,hc,_⟩
    refine ⟨fun i => (c i:ℝ),fun i => Nat.cast_nonneg _,?_⟩
    simpa only [Int.cast_natCast] using (cast_mulVec B (fun i => (c i:ℤ))).trans
      (congrArg (fun z : ι → ℤ => fun j => (z j:ℝ)) hc)

/-- Finite simultaneous parametrization of every lattice point of the
original cone by nonnegative integer coordinates on determinant-one leaves. -/
theorem latticeCone_integral_cover (A : {M : Matrix ι ι ℤ // M.det ≠ 0}) :
    ∃ L : Finset (Matrix ι ι ℤ), (∀ B ∈ L, B.det.natAbs=1) ∧
      ∀ x : ι → ℤ, (fun i => (x i:ℝ)) ∈ latticeCone A.val ↔
        ∃ B ∈ L, ∃! c : ι → ℕ, B *ᵥ (fun i => (c i:ℤ)) = x := by
  obtain ⟨L,hL,hcover⟩ := latticeCone_unimodular_cover A
  refine ⟨L,hL,fun x => ?_⟩
  rw [hcover]
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨B,hB,hx⟩
    exact ⟨B,hB,(unimodularCone_address ⟨B,hL B hB⟩ x).mp hx⟩
  · rintro ⟨B,hB,hx⟩
    exact ⟨B,hB,(unimodularCone_address ⟨B,hL B hB⟩ x).mpr hx⟩

#print axioms unimodularCone_address
#print axioms latticeCone_integral_cover
#print axioms latticeCone_unimodular_cover
end
end GaloisForLFunctions.RepresentationLifting
