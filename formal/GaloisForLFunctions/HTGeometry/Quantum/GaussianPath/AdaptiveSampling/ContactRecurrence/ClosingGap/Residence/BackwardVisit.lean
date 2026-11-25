import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ContactRecurrence.ClosingGap.Residence.AdjacentErrors
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ContactRecurrence.ClosingGap.Residence.Perturbations

/-! # A preceding physical visit from the duration and successive spectral gaps -/

open Set Finset
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactRecurrence.ClosingGap.Residence
open EmptyVisitFlux
noncomputable section

private theorem accumulated_turns {d : ℕ} (w : Fin (d+1) → ℝ) (t : ℝ) (m : Fin d → ℤ) :
    let u (k : Fin d) := t*(w k.succ-w k.castSucc)-(m k:ℝ)
    ∀ i, ((primitive u i+t*w 0:ℝ):UnitAddCircle)=((t*w i:ℝ):UnitAddCircle) := by
  intro u
  apply Fin.induction
  · simp [primitive]
  · intro k ih
    have hz : ((m k:ℝ):UnitAddCircle)=0 := (AddCircle.coe_eq_zero_iff (1:ℝ)).mpr ⟨m k,by simp⟩
    have he : primitive u k.succ+t*w 0=(primitive u k.castSucc+t*w 0)+(t*w k.succ-t*w k.castSucc)-(m k:ℝ) := by
      rw [show primitive u k.succ=primitive u k.castSucc+u k from Fin.induction_succ ..]
      dsimp only [u]
      ring
    rw [he,AddCircle.coe_sub,AddCircle.coe_add,ih,AddCircle.coe_sub,hz,sub_zero]
    abel

/-- A preceding visit lies within the product deadline measured in units
of any chosen adjacent gap. The other gaps contribute according to their
own spacing and the length of the observed visit. -/
theorem backward_visit {d : ℕ} (w : Fin (d+1) → ℝ) (hw : StrictMono w) (p : Fin d)
    {r v h : ℝ} (hr : 0≤r) (hs : r<1/2) (hh : 0<h)
    (hv : ∀ u∈Icc (0:ℝ) h, flow w (v+u)∈enclosingUnitArc r) :
    let g (k : Fin d) := w k.succ-w k.castSucc
    ∃ q : ℕ, 0<q ∧ q≤∏ k : {j : Fin d // j≠p}, ⌈2/(h*g k)⌉₊ ∧
      v+h/2-(q:ℝ)/g p<v ∧ flow w (v+h/2-(q:ℝ)/g p)∈enclosingUnitArc r := by
  intro g
  let Q (k : {j : Fin d // j≠p}) := ⌈2/(h*g k)⌉₊
  have hg (k : Fin d) : 0<g k := sub_pos.mpr (hw (Fin.castSucc_lt_succ (i:=k)))
  have hQ (k) : 0<Q k := Nat.ceil_pos.mpr (div_pos two_pos (mul_pos hh (hg k.val)))
  obtain ⟨q,m,hq,hprod,he,hm⟩ := synchronize_gaps g p (hg p) Q hQ
  let t := (q:ℝ)/g p
  let u (k : Fin d) := t*g k-(m k:ℝ)
  have hb (k : Fin d) : |u k|≤h/2*(w k.succ-w k.castSucc) := by
    change |t*g k-(m k:ℝ)|≤h/2*g k
    by_cases hkp : k=p
    · subst k
      rw [show t*g p=(m p:ℝ) from he,sub_self,abs_zero]
      exact mul_nonneg (div_nonneg hh.le two_pos.le) (hg p).le
    · let j : {l : Fin d // l≠p} := ⟨k,hkp⟩
      refine (hm j).le.trans ?_
      apply (div_le_iff₀ (Nat.cast_pos.mpr (hQ j))).mpr
      have hl := (div_le_iff₀ (mul_pos hh (hg k))).mp (Nat.le_ceil (2/(h*g k)))
      change 1≤h/2*g k*(Q j:ℝ)
      change 2≤(Q j:ℝ)*(h*g k) at hl
      linarith only [hl]
  let f (i : Fin (d+1)) := -(primitive u i+t*w 0)
  have hf (i j) : |f i-f j|≤h/2*|w i-w j| := by
    wlog hij : i≤j generalizing i j
    · simpa only [abs_sub_comm (f j) (f i),abs_sub_comm (w j) (w i)] using this j i (le_of_not_ge hij)
    rw [abs_of_nonpos (sub_nonpos.mpr (hw.monotone hij)),show f i-f j=primitive u j-primitive u i by dsimp [f]; ring,neg_sub]
    exact primitive_lipschitz w u _ hb hij
  have hmem := (residence_iff_lipschitz_shifts w hr hs hh.le).mp hv f hf
  have hturn (i) : flow w (v+h/2) i+(f i:UnitAddCircle)=flow w (v+h/2-t) i := by
    rw [show (f i:UnitAddCircle)= -((t*w i:ℝ):UnitAddCircle) by
      change ((-(primitive u i+t*w 0):ℝ):UnitAddCircle)=_
      rw [AddCircle.coe_neg,accumulated_turns w t m]]
    simp only [flow,←sub_eq_add_neg,←AddCircle.coe_sub,sub_mul]
  have hstart := hv 0 ⟨le_rfl,hh.le⟩
  rw [add_zero] at hstart
  obtain ⟨y,b,hy,hspan⟩ := (arc_iff_lifts _ hr).mp hstart
  have hd := end_span w hr hs hh.le hv hy hspan p.succ p.castSucc
  have hwid : h*g p≤2*r := by dsimp only [g]; linarith only [hd,hspan p.castSucc p.succ]
  have hq1 : 1≤(q:ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hq)
  have ht : h/2<t := (lt_div_iff₀ (hg p)).mpr (by linarith only [hwid,hs,hq1])
  exact ⟨q,hq,hprod,by linarith only [ht],by simpa only [hturn] using hmem⟩

#print axioms backward_visit
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactRecurrence.ClosingGap.Residence
