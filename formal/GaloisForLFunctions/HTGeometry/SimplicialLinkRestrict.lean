import GaloisForLFunctions.HTGeometry.SimplicialCochainComplex

/-!
# Restricting a cochain to the link of a face

Garland's method reads a `k`-cochain through the links of the `(k-1)`-faces: over a face `σ` the
cochain becomes the function `u ↦ f(σ ∪ {u})` on the vertices of the link, and the coboundary of `f`
on `σ ∪ {u, u'}` contains the difference of the two link values.  The sign that makes this work is
the incidence sign of `u` in `σ ∪ {u}`, and the reason it works is the antisymmetry of the incidence
sign under erasing two vertices in the two orders.

* `linkRestrict` : **the restriction of a cochain to the link of a face.**
* `coboundary_link_pair` : **the two link terms of the coboundary are a sign times the difference of
  the link values.**
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {α : Type*} [DecidableEq α] [LinearOrder α]

/-- **The restriction of a cochain to the link of a face**: the value on `σ ∪ {u}`, signed so that
the two link terms of the coboundary combine into a difference. -/
def linkRestrict (f : Finset α → ℝ) (σ : Finset α) (u : α) : ℝ :=
  faceSign ℝ (insert u σ) u * f (insert u σ)

omit [LinearOrder α] in
theorem erase_insert_insert_left {σ : Finset α} {u u' : α} (hu : u ∉ σ) (h : u ≠ u') :
    (insert u (insert u' σ)).erase u = insert u' σ := by
  refine Finset.erase_insert ?_
  rw [Finset.mem_insert]
  exact fun hc => hc.elim h hu

omit [LinearOrder α] in
theorem erase_insert_insert_right {σ : Finset α} {u u' : α} (hu' : u' ∉ σ) (h : u ≠ u') :
    (insert u (insert u' σ)).erase u' = insert u σ := by
  rw [Finset.erase_insert_of_ne h, Finset.erase_insert hu']

theorem linkRestrict_eq {σ : Finset α} (f : Finset α → ℝ) (u : α) :
    f (insert u σ) = faceSign ℝ (insert u σ) u * linkRestrict f σ u := by
  rw [linkRestrict, ← mul_assoc, faceSign_mul_self, one_mul]

/-- **The two link terms of the coboundary combine into a difference of link values.**  For a face
`σ ∪ {u, u'}` the summands of `δf` indexed by `u` and `u'` differ by the incidence-sign
antisymmetry, so their sum is a single sign times `f_σ(u) − f_σ(u')`. -/
theorem coboundary_link_pair {σ : Finset α} {u u' : α} (hu : u ∉ σ) (hu' : u' ∉ σ) (h : u ≠ u')
    (f : Finset α → ℝ) :
    faceSign ℝ (insert u (insert u' σ)) u * f (insert u' σ)
        + faceSign ℝ (insert u (insert u' σ)) u' * f (insert u σ)
      = (faceSign ℝ (insert u (insert u' σ)) u' * faceSign ℝ (insert u σ) u)
        * (linkRestrict f σ u - linkRestrict f σ u') := by
  set τ : Finset α := insert u (insert u' σ) with hτ
  have huτ : u ∈ τ := Finset.mem_insert_self _ _
  have hu'τ : u' ∈ τ := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hanti := faceSign_mul_faceSign_erase_antisymm (F := ℝ) huτ hu'τ h
  rw [erase_insert_insert_left hu h, erase_insert_insert_right hu' h] at hanti
  have hAP : faceSign ℝ τ u * faceSign ℝ (insert u' σ) u'
      = -(faceSign ℝ τ u' * faceSign ℝ (insert u σ) u) :=
    eq_neg_of_add_eq_zero_left hanti
  rw [linkRestrict_eq (σ := σ) f u, linkRestrict_eq (σ := σ) f u']
  rw [← mul_assoc, ← mul_assoc, hAP]
  ring

/-- **The coboundary of a cochain, localized at a face.**  On `σ ∪ {u, u'}` the coboundary splits
into the link difference at `σ` and the terms indexed by the vertices of `σ` itself. -/
theorem coboundary_link_decomp {σ : Finset α} {u u' : α} (hu : u ∉ σ) (hu' : u' ∉ σ) (h : u ≠ u')
    (f : Finset α → ℝ) :
    simplicialCoboundary ℝ f (insert u (insert u' σ))
      = (faceSign ℝ (insert u (insert u' σ)) u' * faceSign ℝ (insert u σ) u)
          * (linkRestrict f σ u - linkRestrict f σ u')
        + ∑ v ∈ σ, faceSign ℝ (insert u (insert u' σ)) v
            * f ((insert u (insert u' σ)).erase v) := by
  have hmem : u ∉ insert u' σ := by
    rw [Finset.mem_insert]
    exact fun hc => hc.elim h hu
  rw [simplicialCoboundary_apply, Finset.sum_insert hmem, Finset.sum_insert hu',
    erase_insert_insert_left hu h, erase_insert_insert_right hu' h, ← add_assoc,
    coboundary_link_pair hu hu' h f]


end

end GaloisForLFunctions.HTGeometry
