import GaloisForLFunctions.SignedArithmeticCorrespondences.WeilMassOnDilatedCombWindows
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheRiemannHypothesisIsTheSignOfWeilsFormOnStepPackets

/-!
# The spacing threshold for divergent Weil mass floors

The flat divisor on the whole dyadic window has a finite unit-spacing
Rayleigh limit. Every fixed-ratio window containing it therefore has an
upper bound on its uniform floor. At every larger integer spacing the
floor tends to infinity even on arbitrary subcombs.
-/

noncomputable section
namespace GaloisForLFunctions.SignedArithmeticCorrespondences
open Finset Filter Topology AbsoluteGeometryOfSpecZ HodgeTheoryOfAFixedPart
open scoped ArithmeticFunction.vonMangoldt

/-- Exact dilation law for the whole square. The part with no reciprocal
spacing is the diagonal minus prime incidence. The pole plane and real
jets occur with the same factor as the base square. -/
theorem full_comb_dilation (d : ℕ+) (S : Finset ℕ) (hS : ∀ n ∈ S, 0<n) (c : ℕ → ℝ) :
    let f := fun n => (d:ℕ)*n
    let u := fun n => c (f n)
    let D := ∑ n ∈ S, u n^2*counterterm n
    let P := ∑ n ∈ S, ∑ m ∈ S.erase n, u m*u n*HodgeTheoryOfAFixedPart.contact m n
    combForm (S.image f) c = combForm S u/(d:ℝ)+(1-1/(d:ℝ))*(D-P)+
      (∑ n ∈ S, u n^2)*Real.log d := by
  intro f u D P
  have hf : Function.Injective f := fun _ _ e => Nat.eq_of_mul_eq_mul_left d.pos e
  have hs (T : Finset ℕ) (h : ℕ → ℝ) : ∑ i ∈ T.image f, h i = ∑ j ∈ T, h (f j) :=
    sum_image (fun _ _ _ _ e => hf e)
  let J := ∑ n ∈ S, ∑ m ∈ S.erase n, u m*u n*jetKernel m n
  let M := ∑ n ∈ S, u n^2
  have hbase : combPairing S u = J+P-D := by
    simp only [combPairing,pairKernel,mul_add,sum_add_distrib,J,P,D]
  have hc (m n : ℕ) : HodgeTheoryOfAFixedPart.contact (f m) (f n) =
      HodgeTheoryOfAFixedPart.contact m n := ratioContact_dilate (fun k => Λ k) d m n
  have row (n : ℕ) :
      ∑ m ∈ (S.image f).erase (f n), c m*c (f n)*pairKernel m (f n) =
        (∑ m ∈ S.erase n, u m*u n*jetKernel m n)/(d:ℝ)+
          ∑ m ∈ S.erase n, u m*u n*HodgeTheoryOfAFixedPart.contact m n := by
    rw [← image_erase hf,hs,sum_div,← sum_add_distrib]
    refine sum_congr rfl fun m _ => ?_
    rw [pairKernel,hc,show jetKernel (f m) (f n)=jetKernel m n/(d:ℝ) from jetKernel_dilate d m n]
    dsimp only [u]
    ring
  have hdiag (n : ℕ) (hn : n∈S) : c (f n)^2*counterterm (f n) =
      u n^2*counterterm n+u n^2*Real.log d := by
    rw [show counterterm (f n)=counterterm n+Real.log d from counterterm_dilate d (hS n hn),mul_add]
  have hnew : combPairing (S.image f) c = J/(d:ℝ)+P-(D+M*Real.log d) := by
    simp only [combPairing,hs,row,sum_congr rfl hdiag,sum_add_distrib,J,P,D,M,sum_div,sum_mul]
  rw [combForm,combForm,hbase,hnew,pole_plane_dilate]
  change _ = _+(1-1/(d:ℝ))*(D-P)+M*Real.log d
  ring

private theorem dyadic_value :
    2*Real.log 2-(flatPairing 2 2-2*flatPairing 1 2+flatPairing 1 1) =
      3*Real.log 3-Real.log (4*Real.pi)-Real.eulerMascheroniConstant := by
  rw [flatPairing_self (a := 2) (by decide),flatPairing_self (a := 1) (by decide)]
  have hl : Real.log (4*Real.pi) = Real.log 2+Real.log (2*Real.pi) := by
    rw [show (4:ℝ)*Real.pi=2*(2*Real.pi) by ring,Real.log_mul (by norm_num) (by positivity)]
  norm_num [flatPairing]
  linarith only [hl]

/-- Rayleigh limit of the actual flat integral divisor on (N,2N]. No
prime power has a nonzero overlap on this window. -/
theorem flat_dyadic_comb_limit :
    Tendsto (fun N : ℕ => combForm (Ioc N (N+N)) (fun _ => 1)/(N:ℝ)) atTop
      (𝓝 (3*Real.log 3-Real.log (4*Real.pi)-Real.eulerMascheroniConstant)) := by
  rw [← dyadic_value]
  have h := tendsto_combForm_blockFunction_div (R := 1) (J := 1) (Q := 2)
    (by decide) (by decide) (fun _ => 1)
  have hp : stepPacket 1 1 (fun _ => 1) = flatPacket 1 2 := by
    funext x
    simp [stepPacket]
  rw [hp,packetForm_flatPacket_eq (a := 1) (b := 2) (by decide) (by decide) 2] at h
  norm_num at h
  simpa only [one_mul,mul_one] using h

/-- For each window ratio at least two, spacing one is the unique positive
integer spacing at which uniform coefficient-mass floors cannot diverge. -/
theorem arbitrarily_large_comb_floor_iff (d Q : ℕ+) :
    (∀ B : ℝ, ∀ᶠ N : ℕ in atTop, ∀ S : Finset ℕ, S ⊆ Ioc N (N+(Q:ℕ)*N) →
      ∀ c : ℕ → ℝ, let T := S.image (fun n => (d:ℕ)*n)
        B*(∑ n ∈ T, c n^2) ≤ combForm T c) ↔ 2≤(d:ℕ) := by
  refine ⟨?_,fun hd B => eventually_dilated_comb_floor d hd Q B⟩
  intro h
  by_contra! hd
  have hd₁ : (d:ℕ)=1 := by have := d.pos; omega
  let E := 3*Real.log 3-Real.log (4*Real.pi)-Real.eulerMascheroniConstant
  have hu : ∀ᶠ N : ℕ in atTop, combForm (Ioc N (N+N)) (fun _ => 1)/(N:ℝ)<E+1 :=
    flat_dyadic_comb_limit.eventually (Iio_mem_nhds (show E<E+1 by linarith))
  obtain ⟨N, hN, hlow, hhigh⟩ := ((eventually_ge_atTop 1).and ((h (E+1)).and hu)).exists
  have hs : Ioc N (N+N) ⊆ Ioc N (N+(Q:ℕ)*N) :=
    Ioc_subset_Ioc le_rfl (Nat.add_le_add_left (Nat.le_mul_of_pos_left N Q.pos) N)
  have hmass : (E+1)*(N:ℝ) ≤ combForm (Ioc N (N+N)) (fun _ => 1) := by
    simpa [hd₁,Nat.card_Ioc] using hlow (Ioc N (N+N)) hs (fun _ => 1)
  exact (not_lt_of_ge ((le_div_iff₀ (Nat.cast_pos.mpr hN : (0:ℝ)<N)).mpr hmass)) hhigh

#print axioms flat_dyadic_comb_limit
#print axioms full_comb_dilation
#print axioms arbitrarily_large_comb_floor_iff
end GaloisForLFunctions.SignedArithmeticCorrespondences
