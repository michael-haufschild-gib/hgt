import GaloisForLFunctions.HTGeometry.SiteSupportedEvolutionFactorization
import GaloisForLFunctions.HTGeometry.FintypeSortedSpectrum
import GaloisForLFunctions.RHTower.AutonomousReturnReflection

/-! # Infinite-temperature correlations on disjoint site sets -/
open Matrix
open scoped Kronecker
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
    {A : V → Type*} [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)] [∀ v, Nonempty (A v)]

/-- At infinite temperature the two-point function of observables on
disjoint sites factors, even when each observable entangles its own sites. -/
theorem disjoint_trace_product {S T : Finset V} (hd : Disjoint S T)
    {H K : Matrix ((v : V) → A v) ((v : V) → A v) ℂ}
    (hH : IsSiteSupported S H) (hK : IsSiteSupported T K) :
    (Fintype.card ((v : V) → A v):ℂ)*(H*K).trace=H.trace*K.trace := by
  obtain ⟨B,rfl⟩ := exists_liftLocalMatrix_of_isSiteSupported hH
  obtain ⟨C,rfl⟩ := exists_liftLocalMatrix_of_isSiteSupported hK
  let e := configurationSplitEquiv A S
  let Φ := Matrix.reindexAlgEquiv ℂ ℂ e
  let L := LocalConfiguration A S
  let R := OutsideConfiguration A S
  let C' := liftLocalMatrixOutsideDisjoint hd C
  have hb : Φ (liftLocalMatrix S B)=B ⊗ₖ (1 : Matrix R R ℂ) :=
    reindex_liftLocalMatrix_eq_kronecker_one S B
  have hc : Φ (liftLocalMatrix T C)=(1 : Matrix L L ℂ) ⊗ₖ C' :=
    reindex_liftLocalMatrix_disjoint_eq_one_kronecker hd C
  have tr (X : Matrix ((v : V) → A v) ((v : V) → A v) ℂ) : X.trace=(Φ X).trace :=
    (trace_reindex_eq e X).symm
  have dim : Fintype.card ((v : V) → A v)=Fintype.card L*Fintype.card R := by
    rw [Fintype.card_congr e,Fintype.card_prod]
  rw [tr (liftLocalMatrix S B*liftLocalMatrix T C),tr (liftLocalMatrix S B),tr (liftLocalMatrix T C),
    map_mul,hb,hc,←Matrix.mul_kronecker_mul,mul_one,one_mul,dim]
  simp only [Matrix.trace_kronecker,Matrix.trace_one,Nat.cast_mul]
  ring

/-- On the Choi vector of a unitary, centered right actions supported on
disjoint blocks give orthogonal fluctuations. The actions may be complex. -/
theorem disjoint_choi_fluctuations {S T : Finset V} (hd : Disjoint S T)
    {U H K : Matrix ((v : V) → A v) ((v : V) → A v) ℂ} (hu : Uᴴ*U=1)
    (hH : IsSiteSupported S H) (hK : IsSiteSupported T K) :
    let x := RHTower.choiVector U
    let y := RHTower.choiVector (U*H)
    let z := RHTower.choiVector (U*K)
    inner ℂ (y-inner ℂ x y • x) (z-inner ℂ x z • x)=0 := by
  intro x y z
  let d : ℂ := Fintype.card ((v : V) → A v)
  have hn : d≠0 := Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  have cancel (B : Matrix ((v : V) → A v) ((v : V) → A v) ℂ) : Uᴴ*(U*B)=B := by
    rw [←mul_assoc,hu,one_mul]
  have hxy : inner ℂ x y=H.trace/d := by rw [RHTower.inner_choiVector Fintype.card_pos,cancel]
  have hxz : inner ℂ x z=K.trace/d := by rw [RHTower.inner_choiVector Fintype.card_pos,cancel]
  have hyx : inner ℂ y x=star (H.trace/d) := by
    rw [←hxy]
    exact (inner_conj_symm y x).symm
  have hxx : inner ℂ x x=1 := by
    rw [RHTower.inner_choiVector Fintype.card_pos,hu,Matrix.trace_one,div_self hn]
  have hyz : inner ℂ y z=(Hᴴ*K).trace/d := by
    rw [RHTower.inner_choiVector Fintype.card_pos,Matrix.conjTranspose_mul,mul_assoc,cancel]
  have ht := disjoint_trace_product hd (IsSiteSupported.conjTranspose hH) hK
  change d*(Hᴴ*K).trace=Hᴴ.trace*K.trace at ht
  rw [Matrix.trace_conjTranspose] at ht
  simp only [inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,hxx,hxy,hxz,hyx,hyz,
    mul_one,sub_self,mul_zero,sub_zero,starRingEnd_apply,star_div₀,show star d=d by simp [d]]
  field_simp [hn]
  linear_combination ht

#print axioms disjoint_trace_product
#print axioms disjoint_choi_fluctuations
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
