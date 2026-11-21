import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Elimination.LevelPolynomial
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Elimination.LineRoots

/-! # Uniformly many cuts for all signed rational spectral levels on an affine line -/

open MvPolynomial Matrix Set
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section
variable {ι : Type*} [Fintype ι] {D : ℕ}

/-- Evaluation on a packet of roots with weight and selection fixed. -/
def rationalValue (x : ι → ℂ) (E m : Fin D → ℂ) (q d : MvPolynomial (Option ι) ℂ)
    (s : Fin D → Fin D) : ℂ :=
  ∑ i, m i * eval (fun o : Option ι => o.elim (E (s i)) x) q /
    eval (fun o : Option ι => o.elim (E (s i)) x) d

/-- A simple spectrum on which every denominator is nonzero. -/
def regularPacket (x : ι → ℂ) (E : Fin D → ℂ) (d : MvPolynomial (Option ι) ℂ) : Prop :=
  Function.Injective E ∧ ∀ j, eval (fun o : Option ι => o.elim (E j) x) d ≠ 0

private theorem rootProduct_ne_zero_iff (M : Matrix (Fin D) (Fin D) (MvPolynomial ι ℂ))
    (x : ι → ℂ) (E : Fin D → ℂ) (ht : ∀ k : ℕ, eval x (M^k).trace = ∑ j, E j^k)
    (d : MvPolynomial (Option ι) ℂ) :
    eval x (rootProduct M d) ≠ 0 ↔ regularPacket x E d := by
  rw [eval_rootProduct M x E ht,mul_ne_zero_iff,Finset.prod_ne_zero_iff]
  constructor
  · rintro ⟨hV,h⟩
    exact ⟨Matrix.det_vandermonde_ne_zero_iff.mp (fun he => hV (by rw [he]; norm_num)),
      fun i => h i (Finset.mem_univ i)⟩
  · rintro ⟨hi,h⟩
    exact ⟨pow_ne_zero _ (Matrix.det_vandermonde_ne_zero_iff.mpr hi),fun i _ => h i⟩

private def withLevel (z : ι → Polynomial ℂ) (a : ℂ) (o : Option ι) : Polynomial ℂ :=
  o.elim (Polynomial.C a) z

omit [Fintype ι] in
private theorem eval_withLevel (z : ι → Polynomial ℂ) (a t : ℂ) (p : MvPolynomial (Option ι) ℂ) :
    (linePolynomial (withLevel z a) p).eval t =
      eval (fun o : Option ι => o.elim a (fun i => (z i).eval t)) p := by
  rw [eval_linePolynomial]
  apply congrArg (fun x => eval x p)
  funext o
  cases o <;> simp [withLevel]

/-- Choose one cut level in any positive interval. Outside a finite set of
bounded size the packet is regular and every independent root selection
avoids both signs of the chosen level. The bound is independent of the weights. -/
theorem exists_line_level_cuts (M : Matrix (Fin D) (Fin D) (MvPolynomial ι ℂ))
    (hM : ∀ i j, (M i j).totalDegree ≤ 1) (z : ι → Polynomial ℂ) (hz : ∀ i, (z i).natDegree ≤ 1)
    (E : ℝ → Fin D → ℂ) (m : Fin D → ℂ) (q d : MvPolynomial (Option ι) ℂ)
    (ht : ∀ (t : ℝ) (k : ℕ), eval (fun i => (z i).eval (t:ℂ)) (M^k).trace = ∑ j, E t j^k)
    {t₀ : ℝ} (h₀ : regularPacket (fun i => (z i).eval (t₀:ℂ)) (E t₀) d)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∃ c ∈ Ioo a b, ∃ C : Finset ℝ,
      C.card ≤ D*(d.totalDegree+2*D) + 2*((D+2*D*D+1)^D*(1+q.totalDegree+D*d.totalDegree+1)) ∧
      ∀ t ∉ C, let x := fun i => (z i).eval (t:ℂ)
               regularPacket x (E t) d ∧ ∀ s, rationalValue x (E t) m q d s ≠ (c:ℂ) ∧
                 rationalValue x (E t) m q d s ≠ -(c:ℂ) := by
  classical
  let x (t : ℝ) (i : ι) := (z i).eval (t:ℂ)
  let F (t : ℝ) := rationalValue (x t) (E t) m q d
  obtain ⟨c,hc,havoid⟩ := (Ioo_infinite hab).exists_notMem_finset
    (Finset.univ.image fun s : Fin D → Fin D => |(F t₀ s).re|)
  have hc₀ : 0 ≤ c := ha.trans hc.1.le
  have hbad (s) : F t₀ s ≠ (c:ℂ) ∧ F t₀ s ≠ -(c:ℂ) := by
    constructor <;> intro he <;> apply havoid <;>
      exact Finset.mem_image.mpr ⟨s,Finset.mem_univ _,by simp [he,hc₀]⟩
  let P := rationalModeLevel M m q d
  let R := linePolynomial z (rootProduct M d)
  let L (v : ℂ) := linePolynomial (withLevel z v) P
  have hr (t : ℝ) : R.eval (t:ℂ) ≠ 0 ↔ regularPacket (x t) (E t) d := by
    dsimp only [R]
    rw [eval_linePolynomial]
    exact rootProduct_ne_zero_iff M (x t) (E t) (ht t) d
  have hl (v : ℂ) (t : ℝ) (h : regularPacket (x t) (E t) d) :
      (L v).eval (t:ℂ) = 0 ↔ ∃ s, v = F t s := by
    dsimp only [L]
    rw [eval_withLevel]
    exact eval_rationalModeLevel_eq_zero_iff M (x t) (E t) m h.1 (ht t) q d h.2 v
  have hR : R ≠ 0 := fun he => ((hr t₀).mpr h₀) (by rw [he,Polynomial.eval_zero])
  have hL (v : ℂ) (h : ∀ s, F t₀ s ≠ v) : L v ≠ 0 := by
    intro he
    obtain ⟨s,hs⟩ := (hl v t₀ h₀).mp (by rw [he,Polynomial.eval_zero])
    exact h s hs.symm
  have hp := hL (c:ℂ) fun s => (hbad s).1
  have hn := hL (-(c:ℂ)) fun s => (hbad s).2
  let B := (D+2*D*D+1)^D*(1+q.totalDegree+D*d.totalDegree+1)
  have hcard (v : ℂ) : (lineCuts (L v)).card ≤ B := by
    have hv (o : Option ι) : ((withLevel z v) o).natDegree ≤ 1 := by
      cases o with
      | none => simp [withLevel]
      | some i => exact hz i
    apply (lineCuts_card _).trans ((linePolynomial_degree _ hv _).trans ?_)
    exact (Nat.le_succ _).trans (rationalModeLevel_degree M hM m q d)
  let C := lineCuts R ∪ (lineCuts (L (c:ℂ)) ∪ lineCuts (L (-(c:ℂ))))
  refine ⟨c,hc,C,?_,?_⟩
  · have hRcard := (lineCuts_card R).trans ((linePolynomial_degree z hz _).trans (rootProduct_degree M hM d))
    exact (Finset.card_union_le _ _).trans ((Nat.add_le_add hRcard
      ((Finset.card_union_le _ _).trans (Nat.add_le_add (hcard _) (hcard _)))).trans_eq (by
        change D*(d.totalDegree+2*D)+(B+B) = D*(d.totalDegree+2*D)+2*B
        omega))
  · intro t htC
    have hc' : t ∉ lineCuts R ∧ t ∉ lineCuts (L (c:ℂ)) ∧ t ∉ lineCuts (L (-(c:ℂ))) := by
      simpa only [C,Finset.mem_union,not_or] using htC
    have h := (hr t).mp (fun hv => hc'.1 (mem_lineCuts hR hv))
    refine ⟨h,fun s => ⟨fun he => hc'.2.1 (mem_lineCuts hp ((hl _ t h).mpr ⟨s,he.symm⟩)),
      fun he => hc'.2.2 (mem_lineCuts hn ((hl _ t h).mpr ⟨s,he.symm⟩))⟩⟩

#print axioms exists_line_level_cuts
end
end GaloisForLFunctions.HTGeometry.SpectralJets
