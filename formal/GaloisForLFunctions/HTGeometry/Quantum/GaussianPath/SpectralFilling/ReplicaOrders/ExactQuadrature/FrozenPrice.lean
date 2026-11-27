import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.ExactQuadrature.SurvivalShifts
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.ExactQuadrature.DurationPrice
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.ExactQuadrature.FrameWeights
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.Spacing.PhysicalRecords

/-! # Bandwidth and weight prices for calibrating a frozen survival trace -/
open Real Finset Filter MeasureTheory
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ExactQuadrature
noncomputable section
open SharpOccupation

/-- All positive protocols calibrating the shifted order-q normalized
survival trace pay for every distinct occupation energy, on every prefix
of a single typical Gaussian draw. B is the occupation count. -/
theorem gaussian_survival_clock_price :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let K := k+3
      let D := 2^K
      let H : selfAdjoint (Register K) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      let E := H.2.isHermitian.eigenvalues ∘ (qubitConfigFin K).symm
      let w := microcanonicalWeight (Fin D)
      ∀ q m : ℕ,
        let B := (D+q-1).choose q
        ∀ a b : ℝ, a ≤ b → ∀ p t : Fin m → ℝ, (∀ j, 0 ≤ p j) → (∑ j, p j=1) →
        (∀ j, t j∈Set.Icc a b) →
        (∀ u, ∑ j, (p j:ℂ)*twistedFiniteSpectralFidelity w E (fun _ => 1) (u+t j)^q=
          average (frequencies E q).toList (fun s => twistedFiniteSpectralFidelity w E (fun _ => 1) s^q) 0) →
        (π * ((B : ℝ) - 1) ≤ (b-a) * ((q : ℝ) * circuitHamiltonianSpectralWidth H) ∧
          (∀ j, p j * (B : ℝ) ≤ 1) ∧ B ≤ m) := by
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hw k
  intro K D H E w q m B a b hab p t hp hm ht htest
  let X := ReplicaMultiplicityIndex (Fin D) q
  let F (x : X) := replicaMultiplicityEnergy E x.val
  have hcard : Fintype.card X=B := by
    rw [Fintype.card_coe,←Finset.map_sym_eq_piAntidiag,Finset.card_map,Finset.sym_univ,Finset.card_univ,
      Sym.card_sym_eq_choose,Fintype.card_fin]
  have hRigid := (forall_replicaRigidAt_iff_maximallyProjectiveEnergy E).mpr ((hw k).comp_equiv _) q
  have hinj : Function.Injective F := fun x y he => Subtype.ext (hRigid _ x.property _ y.property he)
  have hwpos (i : Fin D) : 0<w i := by dsimp only [w,microcanonicalWeight]; positivity
  have hg (x y : X) : ∑ j, (p j:ℂ)*wave (F x-F y) (t j)=if x=y then 1 else 0 := by
    simpa only [F,hinj.eq_iff] using (survival_shifts_iff w E hwpos q p t).mp htest x.val x.property y.val y.property
  let e := H.2.isHermitian.eigenvalues
  let l := univ.inf' univ_nonempty e
  let r := univ.sup' univ_nonempty e
  have hE (i : Fin D) : E i∈Set.Icc l r :=
    ⟨inf'_le e (mem_univ ((qubitConfigFin K).symm i)),le_sup' e (mem_univ ((qubitConfigFin K).symm i))⟩
  have hD : 0<D := Nat.two_pow_pos _
  let i₀ : Fin D := ⟨0,hD⟩
  have hlr := (hE i₀).1.trans (hE i₀).2
  have hF (x : X) : F x∈Set.Icc ((q:ℝ)*l) ((q:ℝ)*r) := by
    have hsum : ∑ i, (x.val i:ℝ)=q := by exact_mod_cast (mem_piAntidiag.mp x.property).1
    rw [←hsum,Finset.sum_mul,Finset.sum_mul]
    exact ⟨sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hE i).1 (Nat.cast_nonneg _),
      sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hE i).2 (Nat.cast_nonneg _)⟩
  have hspan := duration_price F p t hp hm hab (mul_le_mul_of_nonneg_left hlr (Nat.cast_nonneg _)) ht hF
    (fun x y hxy => (hg x y).trans (if_neg hxy))
  rw [←mul_sub,hcard] at hspan
  have hB : 0<B := Nat.choose_pos (by omega : q≤D+q-1)
  letI : Nonempty X := Fintype.card_pos_iff.mp (by rwa [hcard])
  have hatom (j : Fin m) : p j*(B:ℝ)≤1 := by
    simpa only [hcard] using atom_price F p t hp hg j
  refine ⟨hspan,hatom,?_⟩
  have h := sum_le_sum (s:=univ) (fun j _ => hatom j)
  rw [←Finset.sum_mul,hm,one_mul,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at h
  exact_mod_cast h

#print axioms gaussian_survival_clock_price
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ExactQuadrature
