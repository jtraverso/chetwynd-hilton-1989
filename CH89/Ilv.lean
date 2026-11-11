/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# Weighted prefix sums of lists and alternation

`wsum φ L = Σ_{v ∈ L} φ v`. Prefix sums of lists of nonnegative (resp. nonpositive) weights lie
between `0` and the total; for the alternation `ilv xs ys = x₁ y₁ x₂ y₂ …` of a list of weights
`+1` with a list of weights `−1`, every prefix sum lies between `min 0 (|xs| − |ys|)` and
`max 1 (|xs| − |ys|)`.
-/

@[expose] public section

namespace CH89

variable {α : Type*}

/-- The weighted sum of a list. -/
def wsum (φ : α → ℤ) (L : List α) : ℤ := (L.map φ).sum

section
variable (φ : α → ℤ)

@[simp] theorem wsum_nil : wsum φ [] = 0 := rfl

@[simp] theorem wsum_cons (a : α) (L : List α) : wsum φ (a :: L) = φ a + wsum φ L := by
  simp [wsum]

theorem wsum_append (L L' : List α) : wsum φ (L ++ L') = wsum φ L + wsum φ L' := by
  simp [wsum]

theorem wsum_reverse (L : List α) : wsum φ L.reverse = wsum φ L := by
  simp [wsum, List.sum_reverse]

theorem wsum_take_add_drop (L : List α) (k : ℕ) :
    wsum φ (L.take k) + wsum φ (L.drop k) = wsum φ L := by
  rw [← wsum_append, List.take_append_drop]

theorem wsum_nonneg_take {L : List α} (h : ∀ v ∈ L, 0 ≤ φ v) (k : ℕ) :
    0 ≤ wsum φ (L.take k) ∧ wsum φ (L.take k) ≤ wsum φ L := by
  induction L generalizing k with
  | nil => simp
  | cons a L ih =>
    cases k with
    | zero =>
      simp only [List.take_zero, wsum_nil, le_refl, wsum_cons, true_and]
      have h1 := h a (List.mem_cons_self ..)
      have h2 := (ih (fun v hv => h v (List.mem_cons_of_mem _ hv)) 0).2
      simp only [List.take_zero, wsum_nil] at h2
      omega
    | succ k =>
      simp only [List.take_succ_cons, wsum_cons]
      have h1 := h a (List.mem_cons_self ..)
      have := ih (fun v hv => h v (List.mem_cons_of_mem _ hv)) k
      omega

theorem wsum_nonpos_take {L : List α} (h : ∀ v ∈ L, φ v ≤ 0) (k : ℕ) :
    wsum φ L ≤ wsum φ (L.take k) ∧ wsum φ (L.take k) ≤ 0 := by
  induction L generalizing k with
  | nil => simp
  | cons a L ih =>
    have h1 := h a (List.mem_cons_self ..)
    have ih' := ih (fun v hv => h v (List.mem_cons_of_mem _ hv))
    cases k with
    | zero =>
      have := (ih' 0).1
      simp only [List.take_zero, wsum_nil] at this ⊢
      simp only [wsum_cons]
      omega
    | succ k =>
      simp only [List.take_succ_cons, wsum_cons]
      have := ih' k
      omega

end

/-- Alternation of two lists. -/
def ilv : List α → List α → List α
  | x :: xs, y :: ys => x :: y :: ilv xs ys
  | xs, [] => xs
  | [], ys => ys

@[simp] theorem ilv_nil_left (ys : List α) : ilv [] ys = ys := by cases ys <;> rfl

@[simp] theorem ilv_nil_right (xs : List α) : ilv xs [] = xs := by cases xs <;> rfl

@[simp] theorem ilv_cons_cons (x y : α) (xs ys : List α) :
    ilv (x :: xs) (y :: ys) = x :: y :: ilv xs ys := rfl

theorem ilv_perm (xs ys : List α) : (ilv xs ys).Perm (xs ++ ys) := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys =>
      rw [ilv_cons_cons, List.cons_append]
      refine List.Perm.cons x ?_
      refine (List.Perm.cons y (ih ys)).trans ?_
      exact List.perm_middle.symm

theorem map_ilv {β : Type*} (f : α → β) (xs ys : List α) :
    (ilv xs ys).map f = ilv (xs.map f) (ys.map f) := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys => simp [ih]

theorem wsum_ilv_take (φ : α → ℤ) {xs ys : List α} (hx : ∀ v ∈ xs, φ v = 1)
    (hy : ∀ v ∈ ys, φ v = -1) (k : ℕ) :
    min 0 ((xs.length : ℤ) - ys.length) ≤ wsum φ ((ilv xs ys).take k) ∧
      wsum φ ((ilv xs ys).take k) ≤ max 1 ((xs.length : ℤ) - ys.length) := by
  induction xs generalizing ys k with
  | nil =>
    simp only [ilv_nil_left, List.length_nil, Nat.cast_zero, zero_sub]
    have h1 := wsum_nonpos_take φ (L := ys) (fun v hv => by rw [hy v hv]; omega) k
    have h2 : wsum φ ys = -(ys.length : ℤ) := by
      clear h1
      induction ys with
      | nil => simp
      | cons a L ih =>
        simp only [wsum_cons, List.length_cons, Nat.cast_succ]
        rw [hy a (List.mem_cons_self ..), ih (fun v hv => hy v (List.mem_cons_of_mem _ hv))]
        ring
    constructor
    · rw [← h2]; exact le_trans (min_le_right _ _) h1.1
    · exact le_trans h1.2 (by simp)
  | cons x xs ih =>
    cases ys with
    | nil =>
      simp only [ilv_nil_right, List.length_cons, List.length_nil, Nat.cast_zero, sub_zero]
      have h1 := wsum_nonneg_take φ (L := x :: xs) (fun v hv => by rw [hx v hv]; omega) k
      have h2 : wsum φ (x :: xs) = ((xs.length + 1 : ℕ) : ℤ) := by
        clear h1 ih
        induction xs generalizing x with
        | nil => simp [hx x (List.mem_cons_self ..)]
        | cons a L ih' =>
          rw [wsum_cons, ih' a (fun v hv => hx v (List.mem_cons_of_mem _ hv)),
            hx x (List.mem_cons_self ..)]
          simp only [List.length_cons]; push_cast; ring
      rw [h2] at h1
      push_cast at h1 ⊢
      constructor
      · exact le_trans (min_le_left _ _) h1.1
      · exact le_trans h1.2 (le_max_right _ _)
    | cons y ys =>
      have hx1 := hx x (List.mem_cons_self ..)
      have hy1 := hy y (List.mem_cons_self ..)
      have ih' := fun k => ih (ys := ys) (fun v hv => hx v (List.mem_cons_of_mem _ hv))
        (fun v hv => hy v (List.mem_cons_of_mem _ hv)) k
      simp only [List.length_cons, Nat.cast_succ]
      have e : ((xs.length : ℤ) + 1 - (ys.length + 1)) = (xs.length : ℤ) - ys.length := by ring
      rw [e, ilv_cons_cons]
      match k with
      | 0 => simp
      | 1 => simp [hx1]
      | j + 2 =>
        simp only [List.take_succ_cons, wsum_cons, hx1, hy1]
        have := ih' j
        constructor <;> linarith [this.1, this.2]

end CH89
