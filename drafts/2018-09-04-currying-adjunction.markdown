---
title: The State monad and the currying adjunction
---
<div style="display:none;">
$$\newcommand{cat}{\mathsf}%
\newcommand{id}{\mathrm{id}}%
\newcommand{bind}{\mathbin{\mathrm{\gg=}}}%
\newcommand{hom}{\mathrm{hom}}%
\newcommand{natto}{\Rightarrow}%{\stackrel{\bullet}{\to}}%
\newcommand{Id}{\mathrm{Id}}%
$$
</div>

A few weeks ago, someone mentioned to me that there is essentially
only one adjunction of endofunctors of $\cat{Set}$. For every set $S$,
the functor $-\times S$ is left adjoint to the functor $\hom(S,-)$,
where the adjunction

$$\Phi^S_{AB} : \hom(A\times S, B)\to\hom(A,\hom(S, B))$$

takes a map $\varphi : A\times S\to B$ to its *curried* version
$A\to\hom(S, B), a\mapsto(s\mapsto \varphi(a,s))$. The reason that
this is essentially the only adjunction of this kind goes roughly as
follows:

Let $F$, $G$ be endofunctors of $\cat{Set}$, $F\dashv G$, with unit
$\eta$ and counit $\varepsilon$. Then there is a natural isomorphism
of sets, the adjunction map, $\Phi_{AB} : \hom(FA,
B)\to\hom(A,GB)$. The central element of the argument is the
following: Choose a singleton set $I = \{*\}$, and let, for all sets
$B$, $e_B : \hom(I, B)\to B$ the the evaluation map,
i.e. $e_B(\varphi) = \varphi(*)$. Then $e$ is a natural isomorphism,
so we obtain an isomorphism $\hom(FI, B)\cong\hom(I,GB)\cong GB$. This
means that $G$ is a *representable functor* represented by the set
$FI$:

$$G \cong \hom(FI, -)$$

If we now apply the functor $\hom(A, -)$ and use the given adjunction
and the currying adjunction, we obtain

$$\hom(FA, B)\cong \hom(A, GB)\cong \hom(A,\hom(FI, B)) \cong
\hom(A\times FI, B),$$

and by the Yoneda Lemma this implies an isomorphism

$$F \cong -\times FI.$$

This means that, up to isomorphism of functors, every pair of adjoint
functors in $\mathsf{Set}$ arises by choosing a set $S$ and setting
$FI := S$.

Now, we know that every adjunction $F\dashv G$ gives rise to a monad
$M = G\circ F$, whose unit $\eta$ is just the unit of the adjunction,
and whose multiplication is derived from the counit, $\mu =
G\bullet\varepsilon\bullet F$. For example, the currying adjunction
gives rise to the *state* monad $\mathrm{St}^S = \hom(S,-)\circ
-\times S = \hom(S, -\times S)$. And from the above discussion it is
clear that there is an *isomorphism of functors* $f :
M\stackrel{\sim}{\natto} \mathrm{St}^{FI}$.

**Question**: Is $f$ an isomorphism *of monads*?

# Preparations

Let $(M,\eta,\mu)$ and $(M',\eta',\mu')$ be monads of a category $C$,
and let $f : M\natto M'$ be a natural transformation, i.e. a morphism
of endofunctors. We say $f$ is a *morphism of monads* if it is
compatible with the units and the multiplications, in the sense that the following diagrams commute:

$$\require{AMScd}
\begin{CD}
\Id @= \Id\\
@V{\eta}VV  @V{\eta'}VV\\
M @>{f}>> M'
\end{CD}$$

and

$$
\begin{CD}
M\circ M @>{f\bullet f}>> M'\circ M'\\
@V{\mu}VV                  @V{\mu'}VV\\
M        @>{f}>>          M'
\end{CD}$$

So far we only know that there is *some* isomorphism of functors $f :
M\natto \mathrm{St}^S$. What we have to do is therefore: First, walk
through the argument again, recording the maps at each step to find an
explicit description of $f$. Then, see if we can check the
compatibility conditions. This is going to be a bit of work ...

# Let's go

Recall that the adjunction map can be written in terms of the unit and
counit as follows: $\Phi_{AB}(\varphi) = G(\varphi)\circ\eta_A$, and
$\Phi_{AB}^{-1}(\psi) = \varepsilon_B\circ F(\psi)$.

Also recall the natural isomorphism given by the evaluation map $e_B:
\hom(I, B)\to B, \varphi\mapsto\varphi(*)$.

So we have a natural isomorphism

$$e_{GB}\circ\Phi_{IB} : \hom(FI, B)
\xrightarrow{\Phi_{IB}} \hom(I, GB) \xrightarrow{e_{GB}} GB.$$

Let $\alpha : G\natto\hom(FI,-)$ be the inverse of that, $\alpha_A(x)
= \Phi^{-1}_{IB}(e_{GB}^{-1}(x)) = \varepsilon_B\circ F(*\mapsto
x)$. We're going to need the inverse of that, too, it's
$\alpha^{-1}_A(\varphi) = G(\varphi)(\eta_I(*))$.

Apply the functor $\hom(A, -)$ and compose with $\Phi$ and the
currying map $\Phi^{FI}$, this yields an isomorphism

$$\begin{align*}
\hom(A\times FI, B)&\xrightarrow{\Phi^{FI}_{AB}} \hom(A,\hom(FI, B))\xrightarrow{\alpha^{-1}_B\circ-} \hom(A, GB)\xrightarrow{\Phi^{-1}_{AB}} \hom(FA, B),\\
\varphi &\mapsto \varepsilon_B \circ F(\alpha^{-1}_B\circ \Phi^{FI}_{AB}(\varphi))\\
&= \varepsilon_B\circ F(a\mapsto G(x\mapsto\varphi(a,x))(\eta_I(*))).
\end{align*}$$

By applying it to the identity on $A\times FI$, we obtain an
isomorphism

$$\begin{align*}
\beta_A &: FA \to A\times FI,\\
\beta_A &= \varepsilon_{A\times FI} \circ F(a\mapsto G(x\mapsto (a,x))(\eta_I(*))).
\end{align*}$$

We can now form the horizontal composition $f = \alpha\bullet
\beta : GF \natto \hom(FI, -\times FI)$. Recall the diagram

$$
\begin{CD}
GFA @>{G(\beta_A)}>> G(A\times FI)\\
@V{\alpha_{FA}}VV   @V{\alpha_{A\times FI}}VV\\
\hom(FI, FA) @>{\hom(FI, \beta_A)}>> \hom(FI, A\times FI)
\end{CD}$$

From the two ways to compute this map, the lower path seems to be more
approachable:

$$\begin{align*}
f_A(y) &= \beta_A \circ \alpha_{FA}(y)\\
&= \varepsilon_{A\times FI} \circ F(a\mapsto G(x\mapsto (a, x))(\eta_I(*))) \circ \varepsilon_{FA} \circ F(*\mapsto y)
\end{align*}
$$

This is getting ugly ...

# The "easy" part: Compatibility with the unit

This is the condition $f_A(\eta_A(a)) = \eta^{FI}_A(a)$ for all $a\in
A$. Fearless as we are, let's apply $f_A$ to an argument:

$$f_A(\eta_A(a)) = \varepsilon_{A\times FI} \circ F(a\mapsto
G(x\mapsto (a, x))(\eta_I(*))) \circ \varepsilon_{FA} \circ F(*\mapsto
\eta_A(a))$$

It's time for little simplification. Let $\hat{a}$ denote the constant
map $*\mapsto a$. Then $*\mapsto \eta_A(a)$ can be written as
composition $\eta_A\circ \hat{a}$. This way, the part
$\varepsilon_{FA}\circ F(*\mapsto\eta_A(a))$ becomes $\varepsilon_{FA}
\circ F(\eta_A) \circ F(\hat{a})$, which is just $F(\hat{a})$ by the
triangle equation! We now have

$$
\begin{align*}
f_A(\eta_A(a)) &= \varepsilon_{A\times FI} \circ F(a\mapsto G(x\mapsto (a, x))(\eta_I(*))) \circ F(\hat{a})\\
&= \varepsilon_{A\times FI} \circ F(* \mapsto G(x\mapsto (a, x))(\eta_I(*)))\\
&= \varepsilon_{A\times FI} \circ F(G(x\mapsto (a,x))\circ\eta_I)\\
&= \varepsilon_{A\times FI} \circ FG(x\mapsto (a,x)) \circ F(\eta_I)
\end{align*}$$

Now use naturality of $\varepsilon$:

$$
\begin{align*}
f_A(\eta_A(a)) &= (x\mapsto (a,x)) \circ \varepsilon_{FI} \circ F(\eta_I)\\
&= (x\mapsto (a,x))\\
&= \eta^{FI}_A(a)
\end{align*}
$$

by the triangle equation again!

# Trembling now ... compatibility with multiplication

So now we have to check that $\mu^{FI}_A\circ(f\bullet f) =
f\circ\mu_A$, right? I'm afraid to tackle this directly. Each step
means scribbling more than a line of symbols where you easily lose
track of parentheses. There must be an easier way. Let's look at the
problem again, abstractly.

Say we have two adjoint pairs, $F\dashv G$ and $F'\dashv G'$, and
morphisms $\alpha: G\natto G'$ and $\beta : F\natto F'$, and we want
to prove that the following diagram commutes:

$$\begin{CD}
GFGF @>{\alpha\bullet\beta\bullet\alpha\bullet\beta}>> G'F'G'F'\\
@V{\mu}VV                                              @V{\mu'}VV\\
GF   @>{\alpha\bullet\beta}>>                          G'F'
\end{CD}$$

where $\mu = G\bullet\varepsilon\bullet F$ and $\mu' =
G'\bullet\varepsilon'\bullet F'$. We can employ the *interchange law*
between horizontal and vertical composition, which states (cited from MacLane[^MLNotation]) that

$$(\tau'\circ \sigma')\bullet(\tau\circ \sigma) = (\tau'\bullet\tau)\circ(\sigma'\bullet\sigma)$$

[^MLNotation]: Note that MacLane uses $\circ$ for horizontal and $\cdot$ for vertical composition.

if the compositions make sense. Let's apply this law (with a side of
wishful thinking):

$$\begin{align*}
\mu' \circ (\alpha\bullet\beta\bullet\alpha\bullet\beta) &= (G'\bullet\varepsilon'\bullet F')\circ(\alpha\bullet\beta\bullet\alpha\bullet\beta)\\
&= (G'\bullet(\varepsilon'\bullet F'))\circ(\alpha\bullet(\beta\bullet\alpha\bullet\beta))\\
&= (G'\circ\alpha) \bullet  ((\varepsilon'\bullet F')\circ ((\beta\bullet\alpha)\bullet\beta))\\
&= (G'\circ\alpha) \bullet (\varepsilon' \circ (\beta\bullet\alpha)) \bullet (F'\circ \beta)\\
&= \alpha \bullet (\varepsilon' \circ (\beta\bullet\alpha)) \bullet \beta\\
&\stackrel{?}{=} \alpha \bullet\varepsilon\bullet\beta\\
&= (\alpha\circ G)\bullet((\Id\bullet\Id)\circ \varepsilon)\bullet(\beta\circ F)\\
&= (\alpha\bullet\beta)\circ(G\bullet\varepsilon\bullet F)\\
&= (\alpha\bullet\beta)\circ\mu.
\end{align*}$$

We find that it suffices to prove $\varepsilon =
\varepsilon'\circ(\beta\bullet\alpha)$!

Let's keep the notation $G' = \hom(FI, -)$ and $F' = -\times FI$ for a
bit, along with $\eta'$, $\varepsilon'$ and $\Phi'$. Recall then the
natural transformations $\alpha : G\natto G'$ and $\beta : F\natto
F'$, where $\beta_A$ is the composition

$$
\hom(F'A, B) \xrightarrow{\Phi'_{AB}} \hom(A, G'B) \xrightarrow{\alpha^{-1}_B\circ -} \hom(A, GB) \xrightarrow{\Phi^{-1}_{AB}} \hom(FA, B)
$$

applied to $\id_{F'A}$, that is,

$$\begin{align*}
\beta_A &= \Phi^{-1}_{A,F'A}(\alpha^{-1}_{F'A}\circ \Phi'_{A,F'A}(\id_{F'A}))\\
&= \varepsilon_{F'A}\circ F(\alpha^{-1}_{F'A}\circ \eta'_A)
\end{align*}.$$

Then

$$\begin{align*}
(\varepsilon'\circ(\beta\bullet\alpha))_A &= \varepsilon'_A \circ \beta_{G'A} \circ F(\alpha_A)\\
&= \underline{\varepsilon'_A \circ \varepsilon_{F'G'A}} \circ F(\alpha^{-1}_{F'G'A}\circ \eta'_{G'A} \circ \alpha_A)\\
&= \varepsilon_A \circ FG(\varepsilon'_A) \circ F(\alpha^{-1}_{F'G'A}\circ \eta'_{G'A} \circ \alpha_A)\\
&= \varepsilon_A \circ F(\underline{G(\varepsilon'_A) \circ \alpha^{-1}_{F'G'A}}\circ \eta'_{G'A} \circ \alpha_A)\\
&= \varepsilon_A \circ F(\alpha^{-1}_A\circ \underline{G'(\varepsilon'_A) \circ \eta'_{G'A}} \circ \alpha_A)\\
&= \varepsilon_A \circ F(\alpha^{-1}_A\circ \alpha_A)\\
&= \varepsilon_A
\end{align*}$$

by naturality of $\varepsilon : FG\natto\Id$, $\alpha : G\natto G'$,
and the triangle equation $(G'\bullet\varepsilon') \circ (\eta'\bullet
G') = \id_{G'}$.

This concludes the proof. The morphism $f : GF\to \hom(FI, -\times
FI)$ is an isomorphism of monads.

# Conclusion

So, yeah. What does this mean? I was looking for a way to turn a monad
"inside out" to construct some kind of "dual" comonad. Obviously that
comonad would live in a different category in general, but wouldn't it
be nice if it was in the same category? It turns out that if this
category is $\cat{Set}$, then the only monad that can be built in this
way is the state monad, which, when turned inside out, yields the
"store" comonad, $A\mapsto \hom(S, A)\times S$.

