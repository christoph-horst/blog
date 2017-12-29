---
title: About
---
Nullam imperdiet sodales orci vitae molestie. Nunc quam orci, pharetra a
rhoncus vitae, eleifend id felis. Suspendisse potenti. Etiam vitae urna orci.
Quisque pellentesque dignissim felis, egestas tempus urna luctus vitae. In hac
habitasse platea dictumst. Morbi fringilla mattis odio, et mattis tellus
accumsan vitae.

1. Amamus Unicode 碁
2. Interdum nex magna.
3. Farsi فارسی
4. Math :math:`\exp(i\pi) = -1`
      
Vivamus eget mauris sit amet nulla laoreet lobortis. Nulla in diam elementum
risus convallis commodo. Cras vehicula varius dui vitae facilisis. Proin
elementum libero eget leo aliquet quis euismod orci vestibulum. Duis rhoncus
lorem consequat tellus vestibulum aliquam. Quisque orci orci, malesuada porta
blandit et, interdum nec magna.

RST = restructured text
http://docutils.sourceforge.net/docs/ref/rst/roles.html#math
http://docutils.sourceforge.net/docs/ref/rst/directives.html#code

.. math::
   \begin{vmatrix}
   a & 0 & 0 & \dots & 0\\
   0 & a & 0 & \dots & 0\\
   \vdots & \vdots & \ddots & & \dots\\
   0 & 0 & 0 & \dots & a
   \end{vmatrix} = a^n


.. code:: Haskell

   pandocMathCompiler =
    let mathExtensions = [Ext_tex_math_dollars, Ext_tex_math_double_backslash,
                          Ext_latex_macros]
        defaultExtensions = writerExtensions defaultHakyllWriterOptions
        newExtensions = foldr S.insert defaultExtensions mathExtensions
        writerOptions = defaultHakyllWriterOptions {
                          writerExtensions = newExtensions,
                          writerHTMLMathMethod = MathJax "http://cdn.mathjax.org/mathjax/latest/MathJax.js"
                        }
    in pandocCompilerWithTransform defaultHakyllReaderOptions writerOptions id

   
   
