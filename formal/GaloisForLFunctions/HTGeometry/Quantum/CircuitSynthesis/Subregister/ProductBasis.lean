import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Diagonal.MultiplexedPhases.UnitaryCompiler
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Subregister.Evolution
import GaloisForLFunctions.HTGeometry.SiteSupportedEvolutionFactorization

/-! # Compiling the eigenbasis of two disjoint physical blocks -/
open Matrix Finset
namespace GaloisForLFunctions.HTGeometry.Subregister
open DiagonalSynthesis DiagonalSynthesis.MultiplexedPhases
noncomputable section
private abbrev Cfg (n : ℕ) := Fin n→Bool
variable {n k j : ℕ} {S T : Finset (Fin n)}

private def localConfig (e : Fin k≃S) (x : Cfg n) : Cfg k := fun i => x (e i).val

private theorem place_diagonal (e : Fin k≃S) (p : Cfg k→ℂ) :
    place e (diagonal p)=diagonal (fun x => p (localConfig e x)) := by
  classical
  ext x y
  by_cases h : x=y
  · subst y
    change (if restrictOutsideConfiguration S x=restrictOutsideConfiguration S x then
      diagonal p (localConfig e x) (localConfig e x) else 0)=_
    rw [if_pos rfl,diagonal_apply_eq,diagonal_apply_eq]
  · rw [diagonal_apply_ne _ h]
    by_cases ho : restrictOutsideConfiguration S x=restrictOutsideConfiguration S y
    · have hl : localConfig e x≠localConfig e y := by
        intro hl
        apply h
        funext i
        by_cases hi : i∈S
        · obtain ⟨s,hs⟩ := e.surjective ⟨i,hi⟩
          have he := congrArg Subtype.val hs
          simpa only [localConfig,he] using congrFun hl s
        · exact congrFun ho ⟨i,hi⟩
      change (if restrictOutsideConfiguration S x=restrictOutsideConfiguration S y then
        diagonal p (localConfig e x) (localConfig e y) else 0)=0
      rw [if_pos ho,diagonal_apply_ne _ hl]
    · simp [place,liftLocalMatrix,ho]

private theorem place_star (e : Fin k≃S) (A : Register k) : place e (star A)=star (place e A) := by
  ext x y
  by_cases ho : restrictOutsideConfiguration S x=restrictOutsideConfiguration S y
  · change (if restrictOutsideConfiguration S x=restrictOutsideConfiguration S y then
          star (A (localConfig e y) (localConfig e x)) else 0) =
        star (if restrictOutsideConfiguration S y=restrictOutsideConfiguration S x then
          A (localConfig e y) (localConfig e x) else 0)
    rw [if_pos ho,if_pos ho.symm]
  · change (if restrictOutsideConfiguration S x=restrictOutsideConfiguration S y then
          star (A (localConfig e y) (localConfig e x)) else 0) =
        star (if restrictOutsideConfiguration S y=restrictOutsideConfiguration S x then
          A (localConfig e y) (localConfig e x) else 0)
    rw [if_neg ho,if_neg (Ne.symm ho),star_zero]

private theorem placed_unitary (e : Fin k≃S) (V : unitaryGroup (Cfg k) ℂ) :
    place e (V : Register k)∈unitary (Register n) := by
  have hV := Unitary.mem_iff.mp V.property
  apply Unitary.mem_iff.mpr
  rw [←place_star]
  change (placeHom e) (star (V : Register k))*(placeHom e) V.val=1 ∧
    (placeHom e) V.val*(placeHom e) (star (V : Register k))=1
  rw [←map_mul,←map_mul,hV.1,hV.2,map_one]
  exact ⟨rfl,rfl⟩

/-- In the product of the independently compiled child eigenbases,
the two-block Hamiltonian is exactly diagonal. Idle wires are allowed. -/
theorem disjoint_sum_basis (e : Fin k≃S) (f : Fin j≃T) (hST : Disjoint S T)
    (hk : 2 ≤ k) (hj : 2 ≤ j) {A : Register k} {B : Register j} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ∃ (V : unitaryGroup (Cfg n) ℂ) (d : Cfg n→ℝ),
      Realizes (35*(2^k)^2+35*(2^j)^2) (V : Register n) ∧
      place e A+place f B=(V : Register n)*diagonal (fun i => (d i:ℂ))*star (V : Register n) := by
  let L := hA.eigenvectorUnitary
  let R := hB.eigenvectorUnitary
  let X := place e (L : Register k)
  let Y := place f (R : Register j)
  let V : unitaryGroup (Cfg n) ℂ := ⟨X*Y,mul_mem (placed_unitary e L) (placed_unitary f R)⟩
  let a := fun i => hA.eigenvalues (localConfig e i)
  let b := fun i => hB.eigenvalues (localConfig f i)
  let D := diagonal fun i => (a i:ℂ)
  let E := diagonal fun i => (b i:ℂ)
  have conjugate {q : ℕ} {S' : Finset (Fin n)} (e' : Fin q≃S') {H : Register q} (hH : H.IsHermitian) :
      place e' H=place e' (hH.eigenvectorUnitary : Register q)*
        diagonal (fun i => (hH.eigenvalues (localConfig e' i):ℂ))*star (place e' (hH.eigenvectorUnitary : Register q)) := by
    let Z : Register q := hH.eigenvectorUnitary
    have he : H=Z*diagonal (fun i => (hH.eigenvalues i:ℂ))*star Z := hH.spectral_theorem
    have h := congrArg (placeHom e') he
    rw [map_mul,map_mul] at h
    simpa only [placeHom,MonoidHom.coe_mk,OneHom.coe_mk,place_diagonal,place_star] using h
  have hleft : place e A*X=X*D := by
    rw [show place e A=X*D*star X from conjugate e hA,mul_assoc _ (star X),
      (Unitary.mem_iff.mp (placed_unitary e L)).1,mul_one]
  have hright : place f B*Y=Y*E := by
    rw [show place f B=Y*E*star Y from conjugate f hB,mul_assoc _ (star Y),
      (Unitary.mem_iff.mp (placed_unitary f R)).1,mul_one]
  have commute (U : Register k) (Z : Register j) : Commute (place e U) (place f Z) :=
    commute_of_isSiteSupported_disjoint hST (isSiteSupported_liftLocalMatrix _ _) (isSiteSupported_liftLocalMatrix _ _)
  have hDY : D*Y=Y*D := by
    have hD : place e (diagonal fun i => (hA.eigenvalues i:ℂ))=D :=
      place_diagonal e (fun i => (hA.eigenvalues i:ℂ))
    rw [←hD]
    exact (commute _ _).eq
  have hX : place f B*X=X*place f B := (commute (L : Register k) B).symm.eq
  have hLV : place e A*(X*Y)=(X*Y)*D := by rw [←mul_assoc,hleft,mul_assoc,hDY,←mul_assoc]
  have hRV : place f B*(X*Y)=(X*Y)*E := by rw [←mul_assoc,hX,mul_assoc,hright,←mul_assoc]
  have hdiag : diagonal (fun i => ((a i+b i:ℝ):ℂ))=D+E := by
    dsimp only [D,E]
    rw [diagonal_add]
    exact congrArg diagonal (funext fun i => Complex.ofReal_add (a i) (b i))
  refine ⟨V,fun i => a i+b i,(realizes_place e (quadratic_unitary_gate_cap hk L)).mul
    (realizes_place f (quadratic_unitary_gate_cap hj R)),?_⟩
  have hmul : (place e A+place f B)*(V : Register n)=(V : Register n)*(D+E) := by
    change (place e A+place f B)*(X*Y)=(X*Y)*(D+E)
    rw [add_mul,mul_add,hLV,hRV]
  rw [hdiag,←hmul,mul_assoc,(Unitary.mem_iff.mp V.property).2,mul_one]

#print axioms disjoint_sum_basis
end
end GaloisForLFunctions.HTGeometry.Subregister
