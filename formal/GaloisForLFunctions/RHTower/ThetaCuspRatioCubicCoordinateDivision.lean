import GaloisForLFunctions.RHTower.ThetaCuspRatioCubicSlopeBoundary
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare

def coordinateReset (i : Coord) : Poly →+* Poly :=
  eval₂Hom C (fun j => if j=i then 0 else X j)
@[simp] theorem coordinateReset_C (i : Coord) (c : ℂ) : coordinateReset i (C c)=C c := by
  simp [coordinateReset]
@[simp] theorem coordinateReset_X (i j : Coord) :
    coordinateReset i (X j)=if j=i then 0 else X j := by simp [coordinateReset]

theorem coordinateReset_eval (i : Coord) (P : Poly) (v : Coord → ℂ) :
    eval v (coordinateReset i P)=eval (fun j => if j=i then 0 else v j) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p j hp => by_cases h:j=i <;> simp [hp,h]

theorem coordinate_division_exists (i : Coord) (P : Poly) :
    ∃ Q : Poly, P=X i*Q+coordinateReset i P := by
  induction P using MvPolynomial.induction_on with
  | C c => exact ⟨0,by simp⟩
  | add p q hp hq =>
    obtain ⟨a,ha⟩ := hp
    obtain ⟨b,hb⟩ := hq
    refine ⟨a+b,?_⟩
    rw [map_add]
    conv_lhs => rw [ha,hb]
    ring
  | mul_X p j hp =>
    by_cases hj:j=i
    · subst j
      exact ⟨p,by simp [mul_comm]⟩
    · obtain ⟨a,ha⟩ := hp
      refine ⟨a*X j,?_⟩
      simp only [map_mul,coordinateReset_X,if_neg hj]
      conv_lhs => rw [ha]
      ring

def coordinateQuotient (i : Coord) (P : Poly) : Poly := (coordinate_division_exists i P).choose

theorem coordinate_division (i : Coord) (P : Poly) :
    P=X i*coordinateQuotient i P+coordinateReset i P :=
  (coordinate_division_exists i P).choose_spec

theorem coordinateReset_line (P : Poly) (r : ℂ) :
    affineLine r (coordinateReset Coord.U P)=Polynomial.C (planeValue r P) := by
  apply Polynomial.funext
  intro h
  rw [affineLine_eval,coordinateReset_eval]
  have he : (fun j => if j=Coord.U then (0:ℂ) else basePoint h r 0 j)=basePoint 0 r 0 := by
    funext j
    cases j <;> rfl
  rw [he,Polynomial.eval_C]
  rfl

theorem affineLine_quotient (P : Poly) (r : ℂ) :
    affineLine r (coordinateQuotient Coord.U P)=(affineLine r P).divX := by
  have he := congrArg (affineLine r) (coordinate_division Coord.U P)
  simp only [map_add,map_mul,affineLine_X,affineLineCoord,coordinateReset_line] at he
  apply Polynomial.ext
  intro n
  have hc := congrArg (fun p : Polynomial ℂ => p.coeff (n+1)) he
  simpa [Polynomial.coeff_divX] using hc.symm

end
end HTGeometry.ThetaRatioInfinity
